// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

// The DAO's shape: the value is sent before the balance is cleared, so a callee that calls withdraw again is paid twice.
/// gdp: law the vault holds what it owes: balance >= sum(balances)
contract Vault {
    mapping(address => uint256) public balances;

    function deposit() external payable { balances[msg.sender] += msg.value; }

    function withdraw() external {
        uint256 amount = balances[msg.sender];
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
        balances[msg.sender] = 0;
    }
}
