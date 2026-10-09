# @version ^0.4.3

balanceOf: public(HashMap[address, uint256])
allowance: public(HashMap[address, HashMap[address, uint256]])
totalSupply: public(uint256)

event Transfer:
    sender: indexed(address)
    receiver: indexed(address)
    amount: uint256

event Approval:
    owner: indexed(address)
    spender: indexed(address)
    amount: uint256

@deploy
def __init__(initialSupply: uint256):
    self.balanceOf[msg.sender] = initialSupply
    self.totalSupply = initialSupply
    log Transfer(sender=empty(address), receiver=msg.sender, amount=initialSupply)

@external
def transfer(to: address, amount: uint256) -> bool:
    assert self.balanceOf[msg.sender] >= amount
    self.balanceOf[msg.sender] -= amount
    self.balanceOf[to] += amount
    log Transfer(sender=msg.sender, receiver=to, amount=amount)
    return True

@external
def approve(spender: address, amount: uint256) -> bool:
    self.allowance[msg.sender][spender] = amount
    log Approval(owner=msg.sender, spender=spender, amount=amount)
    return True

@external
def transferFrom(from_: address, to: address, amount: uint256) -> bool:
    currentAllowance: uint256 = self.allowance[from_][msg.sender]
    assert currentAllowance >= amount
    assert self.balanceOf[from_] >= amount
    self.allowance[from_][msg.sender] = currentAllowance - amount
    self.balanceOf[from_] -= amount
    self.balanceOf[to] += amount
    log Transfer(sender=from_, receiver=to, amount=amount)
    return True
