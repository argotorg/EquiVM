import Examples.Ballot.Spec
import Solm.Notation

/-!
# Ballot spec in the Solidity-faithful Solm frontend

The whole Ballot spec (structs, storage aliases, delegation-chain `while`, both `for` loops, and
the auto-generated public getters), written with `solidity%` and proven definitionally equal to
the AST spec in `Examples/Ballot/Spec.lean`.

`to` is a Lean keyword, so the `delegate(address to)` parameter is written `«to»`.
Transition order matches `ballotContract.transitions` (selector order).
-/

open Solm Solm.Notation

namespace Ballot.Syntax

def contractSyntax : ContractDecl := solidity% contract Ballot {
  struct Voter {
    uint256 weight;
    bool voted;
    address delegate;
    uint256 vote;
  }

  struct Proposal {
    bytes32 name;
    uint256 voteCount;
  }

  address chairperson;
  mapping(address => Voter) voters;
  Proposal[] proposals;

  constructor(bytes32[] memory proposalNames) {
    chairperson = msg.sender;
    voters[chairperson].weight = 1;
    for (uint256 i = 0; i < proposalNames.length; i++) {
      proposals.push(Proposal({name: proposalNames[i], voteCount: 0}));
    }
  }

  function vote(uint256 proposal) external {
    Voter storage sender = voters[msg.sender];
    require(sender.weight != 0);
    require(!sender.voted);
    sender.voted = true;
    sender.vote = proposal;
    proposals[proposal].voteCount =
      (proposals[proposal].voteCount + sender.weight) as uint256;
  }

  function proposals(uint256 i) external returns (bytes32, uint256) {
    return (proposals[i].name, proposals[i].voteCount);
  }

  function chairperson() external returns (address) {
    return chairperson;
  }

  function delegate(address «to») external {
    Voter storage sender = voters[msg.sender];
    require(sender.weight != 0);
    require(!sender.voted);
    require(«to» != msg.sender);
    while (voters[«to»].delegate != address(0)) {
      «to» = voters[«to»].delegate;
      require(«to» != msg.sender);
    }
    Voter storage delegate_ = voters[«to»];
    require(delegate_.weight >= 1);
    sender.voted = true;
    sender.delegate = «to»;
    if (delegate_.voted) {
      proposals[delegate_.vote].voteCount =
        (proposals[delegate_.vote].voteCount + sender.weight) as uint256;
    } else {
      delegate_.weight = (delegate_.weight + sender.weight) as uint256;
    }
  }

  function winningProposal() external returns (uint256) {
    uint256 winningProposal_ = 0;
    uint256 winningVoteCount = 0;
    for (uint256 p = 0; p < proposals.length; p++) {
      if (proposals[p].voteCount > winningVoteCount) {
        winningVoteCount = proposals[p].voteCount;
        winningProposal_ = p;
      }
    }
    return winningProposal_;
  }

  function giveRightToVote(address voter) external {
    require(msg.sender == chairperson);
    require(!voters[voter].voted);
    require(voters[voter].weight == 0);
    voters[voter].weight = 1;
  }

  function voters(address a) external returns (uint256, bool, address, uint256) {
    return (voters[a].weight, voters[a].voted, voters[a].delegate, voters[a].vote);
  }

  function winnerName() external returns (bytes32) {
    var w = winningProposal();
    return proposals[w].name;
  }
}

theorem contractSyntax_eq : contractSyntax = Ballot.ballotContract := by rfl

end Ballot.Syntax
