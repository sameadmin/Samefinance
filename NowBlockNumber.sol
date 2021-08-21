// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.6.12;

contract NowBlockNumber {
	function getBlock() view public returns(uint256){
		return block.number;
	}
}
