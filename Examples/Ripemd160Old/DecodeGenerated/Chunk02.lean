import Examples.Ripemd160Old.DecodeGenerated.Chunk01

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes2 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨527⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1))),
  (⟨529⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none)),
  (⟨530⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨531⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨532⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1))),
  (⟨534⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none)),
  (⟨535⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨536⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨537⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none)),
  (⟨538⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none)),
  (⟨539⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨540⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨541⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1))),
  (⟨543⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨544⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨545⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none)),
  (⟨546⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨547⟩, some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none)),
  (⟨548⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨549⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none)),
  (⟨550⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨551⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨966⟩, 2))),
  (⟨554⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨555⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨556⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1))),
  (⟨558⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨559⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨947⟩, 2))),
  (⟨562⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨563⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨564⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1))),
  (⟨566⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨567⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨928⟩, 2))),
  (⟨570⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨571⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨572⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1))),
  (⟨574⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨575⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨909⟩, 2))),
  (⟨578⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨579⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨580⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1))),
  (⟨582⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨583⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨890⟩, 2))),
  (⟨586⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨587⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨588⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨590⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨591⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨871⟩, 2))),
  (⟨594⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨595⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨596⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨598⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨599⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨852⟩, 2))),
  (⟨602⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨603⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨604⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨606⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨607⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨833⟩, 2))),
  (⟨610⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨611⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨612⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1))),
  (⟨614⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨615⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨814⟩, 2))),
  (⟨618⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨619⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨620⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1))),
  (⟨622⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨623⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨795⟩, 2))),
  (⟨626⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨627⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨628⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none)),
  (⟨629⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨630⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨776⟩, 2))),
  (⟨633⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨634⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨635⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1))),
  (⟨637⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨638⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨757⟩, 2))),
  (⟨641⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨642⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨643⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨645⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨646⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨738⟩, 2))),
  (⟨649⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨650⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨651⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨653⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨654⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨719⟩, 2))),
  (⟨657⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨658⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none)),
  (⟨659⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1))),
  (⟨661⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨662⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨700⟩, 2))),
  (⟨665⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨666⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1))),
  (⟨668⟩, some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none)),
  (⟨669⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨682⟩, 2))),
  (⟨672⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none)),
  (⟨673⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨674⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨675⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none))
]

private theorem generatedDecodes2_correct : ∀ i : Fin generatedDecodes2.size,
    decode runtimeBytecode generatedDecodes2[i].1 = generatedDecodes2[i].2 := by
  native_decide

theorem decode_527 : decode runtimeBytecode ⟨527⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨96⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨0, by decide⟩
theorem decode_529 : decode runtimeBytecode ⟨529⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP4), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨1, by decide⟩
theorem decode_530 : decode runtimeBytecode ⟨530⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨2, by decide⟩
theorem decode_531 : decode runtimeBytecode ⟨531⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨3, by decide⟩
theorem decode_532 : decode runtimeBytecode ⟨532⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨64⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨4, by decide⟩
theorem decode_534 : decode runtimeBytecode ⟨534⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP3), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨5, by decide⟩
theorem decode_535 : decode runtimeBytecode ⟨535⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨6, by decide⟩
theorem decode_536 : decode runtimeBytecode ⟨536⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨7, by decide⟩
theorem decode_537 : decode runtimeBytecode ⟨537⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.ADD), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨8, by decide⟩
theorem decode_538 : decode runtimeBytecode ⟨538⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.MSTORE), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨9, by decide⟩
theorem decode_539 : decode runtimeBytecode ⟨539⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨10, by decide⟩
theorem decode_540 : decode runtimeBytecode ⟨540⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨11, by decide⟩
theorem decode_541 : decode runtimeBytecode ⟨541⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨16⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨12, by decide⟩
theorem decode_543 : decode runtimeBytecode ⟨543⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨13, by decide⟩
theorem decode_544 : decode runtimeBytecode ⟨544⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨14, by decide⟩
theorem decode_545 : decode runtimeBytecode ⟨545⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP4), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨15, by decide⟩
theorem decode_546 : decode runtimeBytecode ⟨546⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨16, by decide⟩
theorem decode_547 : decode runtimeBytecode ⟨547⟩ = some (Ethereum.Operation.StopArith (Ethereum.Operation.SAOp.MOD), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨17, by decide⟩
theorem decode_548 : decode runtimeBytecode ⟨548⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨18, by decide⟩
theorem decode_549 : decode runtimeBytecode ⟨549⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH0), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨19, by decide⟩
theorem decode_550 : decode runtimeBytecode ⟨550⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨20, by decide⟩
theorem decode_551 : decode runtimeBytecode ⟨551⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨966⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨21, by decide⟩
theorem decode_554 : decode runtimeBytecode ⟨554⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨22, by decide⟩
theorem decode_555 : decode runtimeBytecode ⟨555⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨23, by decide⟩
theorem decode_556 : decode runtimeBytecode ⟨556⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨1⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨24, by decide⟩
theorem decode_558 : decode runtimeBytecode ⟨558⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨25, by decide⟩
theorem decode_559 : decode runtimeBytecode ⟨559⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨947⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨26, by decide⟩
theorem decode_562 : decode runtimeBytecode ⟨562⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨27, by decide⟩
theorem decode_563 : decode runtimeBytecode ⟨563⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨28, by decide⟩
theorem decode_564 : decode runtimeBytecode ⟨564⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨2⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨29, by decide⟩
theorem decode_566 : decode runtimeBytecode ⟨566⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨30, by decide⟩
theorem decode_567 : decode runtimeBytecode ⟨567⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨928⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨31, by decide⟩
theorem decode_570 : decode runtimeBytecode ⟨570⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨32, by decide⟩
theorem decode_571 : decode runtimeBytecode ⟨571⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨33, by decide⟩
theorem decode_572 : decode runtimeBytecode ⟨572⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨3⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨34, by decide⟩
theorem decode_574 : decode runtimeBytecode ⟨574⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨35, by decide⟩
theorem decode_575 : decode runtimeBytecode ⟨575⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨909⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨36, by decide⟩
theorem decode_578 : decode runtimeBytecode ⟨578⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨37, by decide⟩
theorem decode_579 : decode runtimeBytecode ⟨579⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨38, by decide⟩
theorem decode_580 : decode runtimeBytecode ⟨580⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨4⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨39, by decide⟩
theorem decode_582 : decode runtimeBytecode ⟨582⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨40, by decide⟩
theorem decode_583 : decode runtimeBytecode ⟨583⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨890⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨41, by decide⟩
theorem decode_586 : decode runtimeBytecode ⟨586⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨42, by decide⟩
theorem decode_587 : decode runtimeBytecode ⟨587⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨43, by decide⟩
theorem decode_588 : decode runtimeBytecode ⟨588⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨44, by decide⟩
theorem decode_590 : decode runtimeBytecode ⟨590⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨45, by decide⟩
theorem decode_591 : decode runtimeBytecode ⟨591⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨871⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨46, by decide⟩
theorem decode_594 : decode runtimeBytecode ⟨594⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨47, by decide⟩
theorem decode_595 : decode runtimeBytecode ⟨595⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨48, by decide⟩
theorem decode_596 : decode runtimeBytecode ⟨596⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨49, by decide⟩
theorem decode_598 : decode runtimeBytecode ⟨598⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨50, by decide⟩
theorem decode_599 : decode runtimeBytecode ⟨599⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨852⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨51, by decide⟩
theorem decode_602 : decode runtimeBytecode ⟨602⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨52, by decide⟩
theorem decode_603 : decode runtimeBytecode ⟨603⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨53, by decide⟩
theorem decode_604 : decode runtimeBytecode ⟨604⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨54, by decide⟩
theorem decode_606 : decode runtimeBytecode ⟨606⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨55, by decide⟩
theorem decode_607 : decode runtimeBytecode ⟨607⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨833⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨56, by decide⟩
theorem decode_610 : decode runtimeBytecode ⟨610⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨57, by decide⟩
theorem decode_611 : decode runtimeBytecode ⟨611⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨58, by decide⟩
theorem decode_612 : decode runtimeBytecode ⟨612⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨8⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨59, by decide⟩
theorem decode_614 : decode runtimeBytecode ⟨614⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨60, by decide⟩
theorem decode_615 : decode runtimeBytecode ⟨615⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨814⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨61, by decide⟩
theorem decode_618 : decode runtimeBytecode ⟨618⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨62, by decide⟩
theorem decode_619 : decode runtimeBytecode ⟨619⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨63, by decide⟩
theorem decode_620 : decode runtimeBytecode ⟨620⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨9⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨64, by decide⟩
theorem decode_622 : decode runtimeBytecode ⟨622⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨65, by decide⟩
theorem decode_623 : decode runtimeBytecode ⟨623⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨795⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨66, by decide⟩
theorem decode_626 : decode runtimeBytecode ⟨626⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨67, by decide⟩
theorem decode_627 : decode runtimeBytecode ⟨627⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨68, by decide⟩
theorem decode_628 : decode runtimeBytecode ⟨628⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP15), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨69, by decide⟩
theorem decode_629 : decode runtimeBytecode ⟨629⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨70, by decide⟩
theorem decode_630 : decode runtimeBytecode ⟨630⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨776⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨71, by decide⟩
theorem decode_633 : decode runtimeBytecode ⟨633⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨72, by decide⟩
theorem decode_634 : decode runtimeBytecode ⟨634⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨73, by decide⟩
theorem decode_635 : decode runtimeBytecode ⟨635⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨11⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨74, by decide⟩
theorem decode_637 : decode runtimeBytecode ⟨637⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨75, by decide⟩
theorem decode_638 : decode runtimeBytecode ⟨638⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨757⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨76, by decide⟩
theorem decode_641 : decode runtimeBytecode ⟨641⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨77, by decide⟩
theorem decode_642 : decode runtimeBytecode ⟨642⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨78, by decide⟩
theorem decode_643 : decode runtimeBytecode ⟨643⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨79, by decide⟩
theorem decode_645 : decode runtimeBytecode ⟨645⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨80, by decide⟩
theorem decode_646 : decode runtimeBytecode ⟨646⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨738⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨81, by decide⟩
theorem decode_649 : decode runtimeBytecode ⟨649⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨82, by decide⟩
theorem decode_650 : decode runtimeBytecode ⟨650⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨83, by decide⟩
theorem decode_651 : decode runtimeBytecode ⟨651⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨84, by decide⟩
theorem decode_653 : decode runtimeBytecode ⟨653⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨85, by decide⟩
theorem decode_654 : decode runtimeBytecode ⟨654⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨719⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨86, by decide⟩
theorem decode_657 : decode runtimeBytecode ⟨657⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨87, by decide⟩
theorem decode_658 : decode runtimeBytecode ⟨658⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨88, by decide⟩
theorem decode_659 : decode runtimeBytecode ⟨659⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨14⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨89, by decide⟩
theorem decode_661 : decode runtimeBytecode ⟨661⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨90, by decide⟩
theorem decode_662 : decode runtimeBytecode ⟨662⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨700⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨91, by decide⟩
theorem decode_665 : decode runtimeBytecode ⟨665⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨92, by decide⟩
theorem decode_666 : decode runtimeBytecode ⟨666⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨15⟩, 1)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨93, by decide⟩
theorem decode_668 : decode runtimeBytecode ⟨668⟩ = some (Ethereum.Operation.CompBit (Ethereum.Operation.CBLOp.EQ), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨94, by decide⟩
theorem decode_669 : decode runtimeBytecode ⟨669⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨682⟩, 2)) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨95, by decide⟩
theorem decode_672 : decode runtimeBytecode ⟨672⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPI), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨96, by decide⟩
theorem decode_673 : decode runtimeBytecode ⟨673⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨97, by decide⟩
theorem decode_674 : decode runtimeBytecode ⟨674⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨98, by decide⟩
theorem decode_675 : decode runtimeBytecode ⟨675⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes2] using generatedDecodes2_correct ⟨99, by decide⟩

end Ripemd160Old
