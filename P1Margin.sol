/*

    Copyright 2024 Axor DAO

    Licensed under the Apache License, Version 2.0 (the "License");
    you may not use this file except in compliance with the License.
    You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

    Unless required by applicable law or agreed to in writing, software
    distributed under the License is distributed on an "AS IS" BASIS,
    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
    See the License for the specific language governing permissions and
    limitations under the License.

*/

pragma solidity 0.5.16;
pragma experimental ABIEncoderV2;

import { IERC20 } from "@openzeppelin/contracts/token/ERC20/IERC20.sol";
import { SafeERC20 } from "@openzeppelin/contracts/token/ERC20/SafeERC20.sol";
import { P1FinalSettlement } from "./P1FinalSettlement.sol";
import { P1Getters } from "./P1Getters.sol";
import { P1BalanceMath } from "../lib/P1BalanceMath.sol";
import { P1Types } from "../lib/P1Types.sol";


/**
 * @title P1Margin
 * @author axor
 *
 * @notice Contract for withdrawing and depositing.
 */
contract P1Margin is
    P1FinalSettlement,
    P1Getters
{
    using P1BalanceMath for P1Types.Balance;

    // ============ Events ============

    event LogDeposit(
        address indexed account,
        uint256 amount,
        bytes32 balance
    );

    event LogWithdraw(
        address indexed account,
        address destination,
        uint256 amount,
        bytes32 balance
    );

    // ============ Functions ============

    /**
     * @notice Deposit some amount of margin tokens from the msg.sender into an account.
     * @dev Emits LogIndex, LogAccountSettled, and LogDeposit events.
     *
     * @param  account  The account for which to credit the deposit.
     * @param  amount   the amount of tokens to deposit.
     */
      /*@
       reverts_when _FINAL_SETTLEMENT_ENABLED_ == true;
       reverts_when IERC20(_TOKEN_).balanceOf(account) < amount;
       ensures IERC20(_TOKEN_).balanceOf(account) == \old(IERC20(_TOKEN_).balanceOf(account)) - amount;
       ensures IERC20(_TOKEN_).balanceOf(address(this)) == \old(IERC20(_TOKEN_).balanceOf(address(this))) + amount;
       
       ensures _BALANCES_[account].position == \old(_BALANCES_[account].position);
       ensures _BALANCES_[account].positionIsPositive == \old(_BALANCES_[account].positionIsPositive);
       
       requires _settleAccount(_loadContext(), account).marginIsPositive;
       ensures _settleAccount(_loadContext(), account).margin == \old(_settleAccount(_loadContext(), account).margin) + amount;
    also 
       requires _settleAccount(_loadContext(), account).magrinIsPositve == false && amount >= \old(settleAccount(_loadContext(), account).margin);
       ensures _settleAccount(_loadContext(), account).margin == amount - \old(settleAccount(_loadContext(), account).margin);
       ensures _settleAccount(_loadContext(), account).marginIsPositive == true;
    also
        requires _settleAccount(_loadContext(), account).magrinIsPositve == false && amount < \old(settleAccount(_loadContext(), account).margin);
        ensures _settleAccount(_loadContext(), account).margin == \old(settleAccount(_loadContext(), account).margin) - amount;
        ensures _settleAccount(_loadContext(), account).marginIsPositive == false;

    */
    function deposit(
        address account,
        uint256 amount
    )
        external
        noFinalSettlement
        nonReentrant
    {
        P1Types.Context memory context = _loadContext();
        P1Types.Balance memory balance = _settleAccount(context, account);

        SafeERC20.safeTransferFrom(
            IERC20(_TOKEN_),
            msg.sender,
            address(this),
            amount
        );

        balance.addToMargin(amount);
        _BALANCES_[account] = balance;

        emit LogDeposit(
            account,
            amount,
            balance.toBytes32()
        );
    }

    /**
     * @notice Withdraw some amount of margin tokens from an account to a destination address.
     * @dev Emits LogIndex, LogAccountSettled, and LogWithdraw events.
     *
     * @param  account      The account for which to debit the withdrawal.
     * @param  destination  The address to which the tokens are transferred.
     * @param  amount       The amount of tokens to withdraw.
     */
    /*@
       reverts_when _FINAL_SETTLEMENT_ENABLED_ == true;
       reverts_when hasAccountPermissions(account, msg.sender) == false;
       reverts_when IERC20(_TOKEN_).balanceOf(address(this)) < amount;
       ensures IERC20(_TOKEN_).balanceOf(address(this)) == \old(IERC20(_TOKEN_).balanceOf(address(this))) - amount;
       ensures IERC20(_TOKEN_).balanceOf(account) == \old(IERC20(_TOKEN_).balanceOf(account) + amount;

       ensures _BALANCES_[account].position == \old(_BALANCES_[account].position);
       ensures _BALANCES_[account].positionIsPositive == \old(_BALANCES_[account].positionIsPositive);
    
       requires _settleAccount(_loadContext(), account).magrinIsPositve == false && _isCollateralized(_loadContext(), _BALANCES_[account]);
       ensures _settleAccount(_loadContext(), account).margin == amount + \old(settleAccount(_loadContext(), account).margin);
       ensures _settleAccount(_loadContext(), account).marginIsPositive == false;
    also
       requires _settleAccount(_loadContext(), account).marginIsPositive == true && amount <= \old(settleAccount(_loadContext(), account).margin) && _isCollateralized(_loadContext(), _BALANCES_[account]);
       ensures _settleAccount(_loadContext(), account).margin == \old(_settleAccount(_loadContext(), account).margin) - amount;
       ensures _settleAccount(_loadContext(), account).marginIsPositive == true;
    also 
       
        requires _settleAccount(_loadContext(), account).magrinIsPositve == true && amount > \old(settleAccount(_loadContext(), account).margin) && _isCollateralized(_loadContext(), _BALANCES_[account]);
        ensures _settleAccount(_loadContext(), account).margin == amount - \old(settleAccount(_loadContext(), account).margin);
        ensures _settleAccount(_loadContext(), account).marginIsPositive == false;

    */
    function withdraw(
        address account,
        address destination,
        uint256 amount
    )
        external
        noFinalSettlement
        nonReentrant
    {
        require(
            hasAccountPermissions(account, msg.sender),
            "sender does not have permission to withdraw"
        );

        P1Types.Context memory context = _loadContext();
        P1Types.Balance memory balance = _settleAccount(context, account);

        SafeERC20.safeTransfer(
            IERC20(_TOKEN_),
            destination,
            amount
        );

        balance.subFromMargin(amount);
        _BALANCES_[account] = balance;

        require(
            _isCollateralized(context, balance),
            "account not collateralized"
        );

        emit LogWithdraw(
            account,
            destination,
            amount,
            balance.toBytes32()
        );
    }
}
