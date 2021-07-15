// SPDX-License-Identifier: Unlicensed
pragma solidity ^0.6.12;

library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        uint256 c = a + b;
        require(c >= a, "SafeMath: addition overflow");

        return c;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return sub(a, b, "SafeMath: subtraction overflow");
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b <= a, errorMessage);
        uint256 c = a - b;

        return c;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
        // benefit is lost if 'b' is also tested.
        // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
        if (a == 0) {
            return 0;
        }

        uint256 c = a * b;
        require(c / a == b, "SafeMath: multiplication overflow");

        return c;
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return div(a, b, "SafeMath: division by zero");
    }

    /**
     * @dev Returns the integer division of two unsigned integers. Reverts with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b > 0, errorMessage);
        uint256 c = a / b;
        // assert(a == b * c + a % b); // There is no case in which this doesn't hold

        return c;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return mod(a, b, "SafeMath: modulo by zero");
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * Reverts with custom message when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        require(b != 0, errorMessage);
        return a % b;
    }
}


contract swapTest   {
    using SafeMath for uint256;

    mapping(address => uint256) public _totalOwned;
    mapping(address => uint256) public _userOwned;
    uint256 public _userSupply;
    uint256 public _totalSupply;
    uint256 public _taxFee;
    uint256 private constant MAX = ~uint256(0);
    constructor ( uint256 _supply,uint256 _tax) public {
        _taxFee = _tax;
        _totalSupply = _supply;
        _userSupply = MAX-(MAX%_totalSupply);
        _userOwned[msg.sender] =  _userOwned[msg.sender].add(_userSupply);
        _totalOwned[msg.sender] = _totalOwned[msg.sender].add(_supply);

    }

    function balanceOf(address account) public view returns(uint256){
        return _userOwned[account]/(_userSupply/_totalSupply);
    }

    function _transfer(address fromAddr,address toAddr,uint256 count) public {
        (uint256 rAmount, uint256 rTransferAmount,,uint256 tTransferAmount,uint256 rFee)= _getValues(count);
        _totalOwned[fromAddr]= _totalOwned [fromAddr].sub(count);
        _userOwned[fromAddr] = _userOwned[fromAddr].sub(rAmount);
        _totalOwned[toAddr] = _totalOwned[toAddr].add(tTransferAmount);
        _userOwned[toAddr] = _userOwned[toAddr].add(rTransferAmount);
        _reflectFee(rFee);
    }
    function _reflectFee(uint256 rFee) private {
        _userSupply = _userSupply.sub(rFee);
    }

    //_获取值
    //t金额
    function _getValues(uint256 tAmount) private view returns (uint256, uint256, uint256, uint256, uint256) {
        //_获取T值
        (uint256 tTransferAmount,uint256 tFee) = _getTValues(tAmount);
        //_获取R值
        (uint256 rAmount,uint256 rTransferAmount, uint256 rFee) = _getRValues(tAmount,tFee,_userSupply/_totalSupply );
        //返回(t金额,r转账金额,r费用,t转账金额,t费用,t流动性)
        return (rAmount,rTransferAmount,tFee, tTransferAmount,rFee);
    }

    //获取T值
    //t金额
    function _getTValues(uint256 tAmount) public view returns (uint256,uint256) {
        uint256 tFee = tAmount.mul(_taxFee).div(10 ** 2);
        //t转账金额 = t金额 - t费用 - t流动性
        uint256 tTransferAmount = tAmount;
        //返回(t转账金额，t费用，t流动性)
        return (tTransferAmount,tFee);
    }

    //_获取R值
    //t金额 t费用 t费用 t流动性 当前利率
    function _getRValues(uint256 tAmount, uint256 tFee,  uint256 currentRate) public pure returns (uint256,uint256,uint256) {
        uint256 rFee = tFee.mul(currentRate);
        uint256 rAmount = tAmount.mul(currentRate);
        uint256 rTransferAmount = rAmount.sub(rFee);
        //返回 (r金额,r转账金额,r费用)
        return (rAmount,rTransferAmount,rFee);
    }
}
