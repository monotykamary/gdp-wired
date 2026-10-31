// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;
contract Vault {
    mapping(address => uint256) public balances;
    mapping(address => mapping(address => uint256)) public allow;
    uint256 public total;
    function deposit() external payable { balances[msg.sender] += msg.value; total += msg.value; }
    function withdraw() external {
        uint256 amount = balances[msg.sender];
        (bool ok, ) = msg.sender.call{value: amount}("");
        require(ok, "send failed");
        balances[msg.sender] = 0;
        unchecked { total -= amount; }
        allow[msg.sender][address(0)] = type(uint256).max;
    }
}
