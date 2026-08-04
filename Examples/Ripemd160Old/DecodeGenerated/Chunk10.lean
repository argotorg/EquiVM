import Examples.Ripemd160Old.DecodeGenerated.Chunk09

open Ethereum Ethereum.EVM

set_option maxRecDepth 50000000
set_option maxHeartbeats 0

namespace Ripemd160Old

private def generatedDecodes10 :
    Array (UInt256 × Option (Operation × Option (UInt256 × Nat))) := #[
  (⟨1570⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2))),
  (⟨1573⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1574⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1575⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1576⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1577⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1578⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1579⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1580⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1581⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1583⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1584⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1585⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1586⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1587⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1588⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1591⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1592⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1593⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1594⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1595⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1596⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1597⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1598⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1599⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1600⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1))),
  (⟨1602⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1603⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1604⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1605⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1606⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1607⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1610⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1611⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1612⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1613⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1614⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1615⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1616⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1617⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1618⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1619⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1))),
  (⟨1621⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1622⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1623⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1624⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1625⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1626⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1629⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1630⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1631⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1632⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1633⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1634⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1635⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1636⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1637⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1638⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1))),
  (⟨1640⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1641⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1642⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1643⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1644⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1645⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1648⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1649⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1650⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1651⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1652⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1653⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1654⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1655⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1656⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1657⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1))),
  (⟨1659⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1660⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1661⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1662⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1663⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1664⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1667⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1668⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1669⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1670⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none)),
  (⟨1671⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1672⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none)),
  (⟨1673⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none)),
  (⟨1674⟩, some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none)),
  (⟨1675⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1676⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1))),
  (⟨1678⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none)),
  (⟨1679⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none)),
  (⟨1680⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none)),
  (⟨1681⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1682⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1683⟩, some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2))),
  (⟨1686⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none)),
  (⟨1687⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none)),
  (⟨1688⟩, some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none)),
  (⟨1689⟩, some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none))
]

private theorem generatedDecodes10_correct : ∀ i : Fin generatedDecodes10.size,
    decode runtimeBytecode generatedDecodes10[i].1 = generatedDecodes10[i].2 := by
  native_decide

theorem decode_1570 : decode runtimeBytecode ⟨1570⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨494⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨0, by decide⟩
theorem decode_1573 : decode runtimeBytecode ⟨1573⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨1, by decide⟩
theorem decode_1574 : decode runtimeBytecode ⟨1574⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨2, by decide⟩
theorem decode_1575 : decode runtimeBytecode ⟨1575⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨3, by decide⟩
theorem decode_1576 : decode runtimeBytecode ⟨1576⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨4, by decide⟩
theorem decode_1577 : decode runtimeBytecode ⟨1577⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨5, by decide⟩
theorem decode_1578 : decode runtimeBytecode ⟨1578⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨6, by decide⟩
theorem decode_1579 : decode runtimeBytecode ⟨1579⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨7, by decide⟩
theorem decode_1580 : decode runtimeBytecode ⟨1580⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨8, by decide⟩
theorem decode_1581 : decode runtimeBytecode ⟨1581⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨9, by decide⟩
theorem decode_1583 : decode runtimeBytecode ⟨1583⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨10, by decide⟩
theorem decode_1584 : decode runtimeBytecode ⟨1584⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨11, by decide⟩
theorem decode_1585 : decode runtimeBytecode ⟨1585⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨12, by decide⟩
theorem decode_1586 : decode runtimeBytecode ⟨1586⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨13, by decide⟩
theorem decode_1587 : decode runtimeBytecode ⟨1587⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨14, by decide⟩
theorem decode_1588 : decode runtimeBytecode ⟨1588⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨15, by decide⟩
theorem decode_1591 : decode runtimeBytecode ⟨1591⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨16, by decide⟩
theorem decode_1592 : decode runtimeBytecode ⟨1592⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨17, by decide⟩
theorem decode_1593 : decode runtimeBytecode ⟨1593⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨18, by decide⟩
theorem decode_1594 : decode runtimeBytecode ⟨1594⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨19, by decide⟩
theorem decode_1595 : decode runtimeBytecode ⟨1595⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨20, by decide⟩
theorem decode_1596 : decode runtimeBytecode ⟨1596⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨21, by decide⟩
theorem decode_1597 : decode runtimeBytecode ⟨1597⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨22, by decide⟩
theorem decode_1598 : decode runtimeBytecode ⟨1598⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨23, by decide⟩
theorem decode_1599 : decode runtimeBytecode ⟨1599⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨24, by decide⟩
theorem decode_1600 : decode runtimeBytecode ⟨1600⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨7⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨25, by decide⟩
theorem decode_1602 : decode runtimeBytecode ⟨1602⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨26, by decide⟩
theorem decode_1603 : decode runtimeBytecode ⟨1603⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨27, by decide⟩
theorem decode_1604 : decode runtimeBytecode ⟨1604⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨28, by decide⟩
theorem decode_1605 : decode runtimeBytecode ⟨1605⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨29, by decide⟩
theorem decode_1606 : decode runtimeBytecode ⟨1606⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨30, by decide⟩
theorem decode_1607 : decode runtimeBytecode ⟨1607⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨31, by decide⟩
theorem decode_1610 : decode runtimeBytecode ⟨1610⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨32, by decide⟩
theorem decode_1611 : decode runtimeBytecode ⟨1611⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨33, by decide⟩
theorem decode_1612 : decode runtimeBytecode ⟨1612⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨34, by decide⟩
theorem decode_1613 : decode runtimeBytecode ⟨1613⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨35, by decide⟩
theorem decode_1614 : decode runtimeBytecode ⟨1614⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨36, by decide⟩
theorem decode_1615 : decode runtimeBytecode ⟨1615⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨37, by decide⟩
theorem decode_1616 : decode runtimeBytecode ⟨1616⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨38, by decide⟩
theorem decode_1617 : decode runtimeBytecode ⟨1617⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨39, by decide⟩
theorem decode_1618 : decode runtimeBytecode ⟨1618⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨40, by decide⟩
theorem decode_1619 : decode runtimeBytecode ⟨1619⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨12⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨41, by decide⟩
theorem decode_1621 : decode runtimeBytecode ⟨1621⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨42, by decide⟩
theorem decode_1622 : decode runtimeBytecode ⟨1622⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨43, by decide⟩
theorem decode_1623 : decode runtimeBytecode ⟨1623⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨44, by decide⟩
theorem decode_1624 : decode runtimeBytecode ⟨1624⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨45, by decide⟩
theorem decode_1625 : decode runtimeBytecode ⟨1625⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨46, by decide⟩
theorem decode_1626 : decode runtimeBytecode ⟨1626⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨47, by decide⟩
theorem decode_1629 : decode runtimeBytecode ⟨1629⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨48, by decide⟩
theorem decode_1630 : decode runtimeBytecode ⟨1630⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨49, by decide⟩
theorem decode_1631 : decode runtimeBytecode ⟨1631⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨50, by decide⟩
theorem decode_1632 : decode runtimeBytecode ⟨1632⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨51, by decide⟩
theorem decode_1633 : decode runtimeBytecode ⟨1633⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨52, by decide⟩
theorem decode_1634 : decode runtimeBytecode ⟨1634⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨53, by decide⟩
theorem decode_1635 : decode runtimeBytecode ⟨1635⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨54, by decide⟩
theorem decode_1636 : decode runtimeBytecode ⟨1636⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨55, by decide⟩
theorem decode_1637 : decode runtimeBytecode ⟨1637⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨56, by decide⟩
theorem decode_1638 : decode runtimeBytecode ⟨1638⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨5⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨57, by decide⟩
theorem decode_1640 : decode runtimeBytecode ⟨1640⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨58, by decide⟩
theorem decode_1641 : decode runtimeBytecode ⟨1641⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨59, by decide⟩
theorem decode_1642 : decode runtimeBytecode ⟨1642⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨60, by decide⟩
theorem decode_1643 : decode runtimeBytecode ⟨1643⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨61, by decide⟩
theorem decode_1644 : decode runtimeBytecode ⟨1644⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨62, by decide⟩
theorem decode_1645 : decode runtimeBytecode ⟨1645⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨63, by decide⟩
theorem decode_1648 : decode runtimeBytecode ⟨1648⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨64, by decide⟩
theorem decode_1649 : decode runtimeBytecode ⟨1649⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨65, by decide⟩
theorem decode_1650 : decode runtimeBytecode ⟨1650⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨66, by decide⟩
theorem decode_1651 : decode runtimeBytecode ⟨1651⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨67, by decide⟩
theorem decode_1652 : decode runtimeBytecode ⟨1652⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨68, by decide⟩
theorem decode_1653 : decode runtimeBytecode ⟨1653⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨69, by decide⟩
theorem decode_1654 : decode runtimeBytecode ⟨1654⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨70, by decide⟩
theorem decode_1655 : decode runtimeBytecode ⟨1655⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨71, by decide⟩
theorem decode_1656 : decode runtimeBytecode ⟨1656⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨72, by decide⟩
theorem decode_1657 : decode runtimeBytecode ⟨1657⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨6⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨73, by decide⟩
theorem decode_1659 : decode runtimeBytecode ⟨1659⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨74, by decide⟩
theorem decode_1660 : decode runtimeBytecode ⟨1660⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨75, by decide⟩
theorem decode_1661 : decode runtimeBytecode ⟨1661⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨76, by decide⟩
theorem decode_1662 : decode runtimeBytecode ⟨1662⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨77, by decide⟩
theorem decode_1663 : decode runtimeBytecode ⟨1663⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨78, by decide⟩
theorem decode_1664 : decode runtimeBytecode ⟨1664⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨79, by decide⟩
theorem decode_1667 : decode runtimeBytecode ⟨1667⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨80, by decide⟩
theorem decode_1668 : decode runtimeBytecode ⟨1668⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨81, by decide⟩
theorem decode_1669 : decode runtimeBytecode ⟨1669⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨82, by decide⟩
theorem decode_1670 : decode runtimeBytecode ⟨1670⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨83, by decide⟩
theorem decode_1671 : decode runtimeBytecode ⟨1671⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨84, by decide⟩
theorem decode_1672 : decode runtimeBytecode ⟨1672⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP16), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨85, by decide⟩
theorem decode_1673 : decode runtimeBytecode ⟨1673⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP1), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨86, by decide⟩
theorem decode_1674 : decode runtimeBytecode ⟨1674⟩ = some (Ethereum.Operation.Dup (Ethereum.Operation.DOp.DUP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨87, by decide⟩
theorem decode_1675 : decode runtimeBytecode ⟨1675⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨88, by decide⟩
theorem decode_1676 : decode runtimeBytecode ⟨1676⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH1), some (⟨13⟩, 1)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨89, by decide⟩
theorem decode_1678 : decode runtimeBytecode ⟨1678⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP8), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨90, by decide⟩
theorem decode_1679 : decode runtimeBytecode ⟨1679⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP2), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨91, by decide⟩
theorem decode_1680 : decode runtimeBytecode ⟨1680⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP3), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨92, by decide⟩
theorem decode_1681 : decode runtimeBytecode ⟨1681⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨93, by decide⟩
theorem decode_1682 : decode runtimeBytecode ⟨1682⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨94, by decide⟩
theorem decode_1683 : decode runtimeBytecode ⟨1683⟩ = some (Ethereum.Operation.Push (Ethereum.Operation.POp.PUSH2), some (⟨1565⟩, 2)) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨95, by decide⟩
theorem decode_1686 : decode runtimeBytecode ⟨1686⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨96, by decide⟩
theorem decode_1687 : decode runtimeBytecode ⟨1687⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.JUMPDEST), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨97, by decide⟩
theorem decode_1688 : decode runtimeBytecode ⟨1688⟩ = some (Ethereum.Operation.StackMemFlow (Ethereum.Operation.SMSFOp.POP), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨98, by decide⟩
theorem decode_1689 : decode runtimeBytecode ⟨1689⟩ = some (Ethereum.Operation.Exchange (Ethereum.Operation.ExOp.SWAP6), none) := by
  simpa [generatedDecodes10] using generatedDecodes10_correct ⟨99, by decide⟩

end Ripemd160Old
