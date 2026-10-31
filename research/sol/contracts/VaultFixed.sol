// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The same vault, checks-effects-interactions: the balance is cleared before the value is sent.
/// gdp: law the vault holds what it owes: balance >= sum(balances)
contract VaultFixed {
    mapping(address => uint256) public balances;

    function deposit() external payable { balances[msg.sender] += msg.value; }

    function withdraw() external {
        uint256 amount = balances[msg.sender];
        balances[msg.sender] = 0;
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
    }
}
