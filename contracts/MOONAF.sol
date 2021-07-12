/**
 *Submitted for verification at BscScan.com on 2021-05-22
*/

pragma solidity ^0.6.12;
// SPDX-License-Identifier: Unlicensed
interface IERC20 {

    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `recipient`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `sender` to `recipient` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address sender, address recipient, uint256 amount) external returns (bool);

    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);
}



/**
 * @dev Wrappers over Solidity's arithmetic operations with added overflow
 * checks.
 *
 * Arithmetic operations in Solidity wrap on overflow. This can easily result
 * in bugs, because programmers usually assume that an overflow raises an
 * error, which is the standard behavior in high level programming languages.
 * `SafeMath` restores this intuition by reverting the transaction when an
 * operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 */

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

abstract contract Context {
    function _msgSender() internal view virtual returns (address payable) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes memory) {
        this;
        // silence state mutability warning without generating bytecode - see https://github.com/ethereum/solidity/issues/2691
        return msg.data;
    }
}


/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // According to EIP-1052, 0x0 is the value returned for not-yet created accounts
        // and 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470 is returned
        // for accounts without code, i.e. `keccak256('')`
        bytes32 codehash;
        bytes32 accountHash = 0xc5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470;
        // solhint-disable-next-line no-inline-assembly
        assembly {codehash := extcodehash(account)}
        return (codehash != accountHash && codehash != 0x0);
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        // solhint-disable-next-line avoid-low-level-calls, avoid-call-value
        (bool success,) = recipient.call{value : amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain`call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCall(target, data, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data, string memory errorMessage) internal returns (bytes memory) {
        return _functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value, string memory errorMessage) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        return _functionCallWithValue(target, data, value, errorMessage);
    }

    function _functionCallWithValue(address target, bytes memory data, uint256 weiValue, string memory errorMessage) private returns (bytes memory) {
        require(isContract(target), "Address: call to non-contract");

        // solhint-disable-next-line avoid-low-level-calls
        (bool success, bytes memory returndata) = target.call{value : weiValue}(data);
        if (success) {
            return returndata;
        } else {
            // Look for revert reason and bubble it up if present
            if (returndata.length > 0) {
                // The easiest way to bubble the revert reason is using memory via assembly

                // solhint-disable-next-line no-inline-assembly
                assembly {
                    let returndata_size := mload(returndata)
                    revert(add(32, returndata), returndata_size)
                }
            } else {
                revert(errorMessage);
            }
        }
    }
}

/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * By default, the owner account will be the one that deploys the contract. This
 * can later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
contract Ownable is Context {
    address public _owner;
    address private _previousOwner;
    uint256 private _lockTime;

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);


    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        require(_owner == _msgSender(), "Ownable: caller is not the owner");
        _;
    }

    /**
    * @dev Leaves the contract without owner. It will not be possible to call
    * `onlyOwner` functions anymore. Can only be called by the current owner.
    *
    * NOTE: Renouncing ownership will leave the contract without an owner,
    * thereby removing any functionality that is only available to the owner.
    */
    function renounceOwnership() public virtual onlyOwner {
        emit OwnershipTransferred(_owner, address(0));
        _owner = address(0);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        require(newOwner != address(0), "Ownable: new owner is the zero address");
        emit OwnershipTransferred(_owner, newOwner);
        _owner = newOwner;
    }

    function geUnlockTime() public view returns (uint256) {
        return _lockTime;
    }

    //Locks the contract for owner for the amount of time provided
    function lock(uint256 time) public virtual onlyOwner {
        _previousOwner = _owner;
        _owner = address(0);
        _lockTime = now + time;
        emit OwnershipTransferred(_owner, address(0));
    }

    //Unlocks the contract for owner when _lockTime is exceeds
    function unlock() public virtual {
        require(_previousOwner == msg.sender, "You don't have permission to unlock");
        require(now > _lockTime, "Contract is locked until 7 days");
        emit OwnershipTransferred(_owner, _previousOwner);
        _owner = _previousOwner;
    }
}

// pragma solidity >=0.5.0;

interface IUniswapV2Factory {
    event PairCreated(address indexed token0, address indexed token1, address pair, uint);

    function feeTo() external view returns (address);

    function feeToSetter() external view returns (address);

    function getPair(address tokenA, address tokenB) external view returns (address pair);

    function allPairs(uint) external view returns (address pair);

    function allPairsLength() external view returns (uint);

    function createPair(address tokenA, address tokenB) external returns (address pair);

    function setFeeTo(address) external;

    function setFeeToSetter(address) external;
}


// pragma solidity >=0.5.0;

interface IUniswapV2Pair {
    event Approval(address indexed owner, address indexed spender, uint value);
    event Transfer(address indexed from, address indexed to, uint value);

    function name() external pure returns (string memory);

    function symbol() external pure returns (string memory);

    function decimals() external pure returns (uint8);

    function totalSupply() external view returns (uint);

    function balanceOf(address owner) external view returns (uint);

    function allowance(address owner, address spender) external view returns (uint);

    function approve(address spender, uint value) external returns (bool);

    function transfer(address to, uint value) external returns (bool);

    function transferFrom(address from, address to, uint value) external returns (bool);

    function DOMAIN_SEPARATOR() external view returns (bytes32);

    function PERMIT_TYPEHASH() external pure returns (bytes32);

    function nonces(address owner) external view returns (uint);

    function permit(address owner, address spender, uint value, uint deadline, uint8 v, bytes32 r, bytes32 s) external;

    event Mint(address indexed sender, uint amount0, uint amount1);
    event Burn(address indexed sender, uint amount0, uint amount1, address indexed to);
    event Swap(
        address indexed sender,
        uint amount0In,
        uint amount1In,
        uint amount0Out,
        uint amount1Out,
        address indexed to
    );
    event Sync(uint112 reserve0, uint112 reserve1);

    function MINIMUM_LIQUIDITY() external pure returns (uint);

    function factory() external view returns (address);

    function token0() external view returns (address);

    function token1() external view returns (address);

    function getReserves() external view returns (uint112 reserve0, uint112 reserve1, uint32 blockTimestampLast);

    function price0CumulativeLast() external view returns (uint);

    function price1CumulativeLast() external view returns (uint);

    function kLast() external view returns (uint);

    function mint(address to) external returns (uint liquidity);

    function burn(address to) external returns (uint amount0, uint amount1);

    function swap(uint amount0Out, uint amount1Out, address to, bytes calldata data) external;

    function skim(address to) external;

    function sync() external;

    function initialize(address, address) external;
}

// pragma solidity >=0.6.2;

interface IUniswapV2Router01 {
    function factory() external pure returns (address);

    function WETH() external pure returns (address);

    function addLiquidity(
        address tokenA,
        address tokenB,
        uint amountADesired,
        uint amountBDesired,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB, uint liquidity);

    function addLiquidityETH(
        address token,
        uint amountTokenDesired,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external payable returns (uint amountToken, uint amountETH, uint liquidity);

    function removeLiquidity(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline
    ) external returns (uint amountA, uint amountB);

    function removeLiquidityETH(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountToken, uint amountETH);

    function removeLiquidityWithPermit(
        address tokenA,
        address tokenB,
        uint liquidity,
        uint amountAMin,
        uint amountBMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountA, uint amountB);

    function removeLiquidityETHWithPermit(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountToken, uint amountETH);

    function swapExactTokensForTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);

    function swapTokensForExactTokens(
        uint amountOut,
        uint amountInMax,
        address[] calldata path,
        address to,
        uint deadline
    ) external returns (uint[] memory amounts);

    function swapExactETHForTokens(uint amountOutMin, address[] calldata path, address to, uint deadline)
    external
    payable
    returns (uint[] memory amounts);

    function swapTokensForExactETH(uint amountOut, uint amountInMax, address[] calldata path, address to, uint deadline)
    external
    returns (uint[] memory amounts);

    function swapExactTokensForETH(uint amountIn, uint amountOutMin, address[] calldata path, address to, uint deadline)
    external
    returns (uint[] memory amounts);

    function swapETHForExactTokens(uint amountOut, address[] calldata path, address to, uint deadline)
    external
    payable
    returns (uint[] memory amounts);

    function quote(uint amountA, uint reserveA, uint reserveB) external pure returns (uint amountB);

    function getAmountOut(uint amountIn, uint reserveIn, uint reserveOut) external pure returns (uint amountOut);

    function getAmountIn(uint amountOut, uint reserveIn, uint reserveOut) external pure returns (uint amountIn);

    function getAmountsOut(uint amountIn, address[] calldata path) external view returns (uint[] memory amounts);

    function getAmountsIn(uint amountOut, address[] calldata path) external view returns (uint[] memory amounts);
}



// pragma solidity >=0.6.2;

interface IUniswapV2Router02 is IUniswapV2Router01 {
    function removeLiquidityETHSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline
    ) external returns (uint amountETH);

    function removeLiquidityETHWithPermitSupportingFeeOnTransferTokens(
        address token,
        uint liquidity,
        uint amountTokenMin,
        uint amountETHMin,
        address to,
        uint deadline,
        bool approveMax, uint8 v, bytes32 r, bytes32 s
    ) external returns (uint amountETH);

    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;

    function swapExactETHForTokensSupportingFeeOnTransferTokens(
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external payable;

    function swapExactTokensForETHSupportingFeeOnTransferTokens(
        uint amountIn,
        uint amountOutMin,
        address[] calldata path,
        address to,
        uint deadline
    ) external;
}


contract CoinToken is Context, IERC20, Ownable {
    using SafeMath for uint256;
    using Address for address;

    mapping(address => uint256) private _rOwned;
    mapping(address => uint256) private _tOwned;
    mapping(address => mapping(address => uint256)) private _allowances;
    //_被排除在费用之外
    mapping(address => bool) private _isExcludedFromFee;
    //_被排除
    mapping(address => bool) private _isExcluded;
    //_排除
    address[] private _excluded;

    uint256 private constant MAX = ~uint256(0);
    uint256 private _tTotal;
    //_r总计
    uint256 private _rTotal;
    //_t总费用
    uint256 private _tFeeTotal;

    string private _name;
    string private _symbol;
    uint256 private _decimals;
    //税费
    uint256 public _taxFee;
    //_以前的税费
    uint256 private _previousTaxFee;
    //_流动资金费
    uint256 public _liquidityFee;
    //_先前的流动资金费用
    uint256 private _previousLiquidityFee;

    IUniswapV2Router02 public immutable uniswapV2Router;
    address public immutable uniswapV2Pair;
    //在交换和液化
    bool inSwapAndLiquify;
    //交换和液化启用
    bool public swapAndLiquifyEnabled = true;
    //_max 交易金额
    uint256 public _maxTxAmount;
    //出售 num 代币以增加流动性
    uint256 public numTokensSellToAddToLiquidity;
    //============================== 事件 ==============================
    //交换前的最小代币更新
    event MinTokensBeforeSwapUpdated(uint256 minTokensBeforeSwap);
    //交换和液化已启用更新
    event SwapAndLiquifyEnabledUpdated(bool enabled);
    //交换和液化
    event SwapAndLiquify(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoLiqudity
    );
    //锁掉
    modifier lockTheSwap {
        inSwapAndLiquify = true;
        _;
        inSwapAndLiquify = false;
    }

    constructor (string memory _NAME, string memory _SYMBOL, uint256 _DECIMALS, uint256 _supply, uint256 _txFee, uint256 _lpFee, uint256 _MAXAMOUNT, uint256 SELLMAXAMOUNT, address routerAddress, address tokenOwner) public {
        _name = _NAME;
        _symbol = _SYMBOL;
        _decimals = _DECIMALS;
        _tTotal = _supply * 10 ** _decimals;
        _rTotal = (MAX - (MAX % _tTotal));
        _taxFee = _txFee;
        _liquidityFee = _lpFee;
        _previousTaxFee = _txFee;
        _previousLiquidityFee = _lpFee;
        _maxTxAmount = _MAXAMOUNT * 10 ** _decimals;
        numTokensSellToAddToLiquidity = SELLMAXAMOUNT * 10 ** _decimals;


        _rOwned[tokenOwner] = _rTotal;

        IUniswapV2Router02 _uniswapV2Router = IUniswapV2Router02(routerAddress);
        // Create a uniswap pair for this new token 为这个新令牌创建一个 uniswap 对
        uniswapV2Pair = IUniswapV2Factory(_uniswapV2Router.factory())
        .createPair(address(this), _uniswapV2Router.WETH());

        // set the rest of the contract variables 设置其余的合约变量
        uniswapV2Router = _uniswapV2Router;

        //exclude owner and this contract from fee 从费用中排除所有者和本合同
        _isExcludedFromFee[tokenOwner] = true;
        _isExcludedFromFee[address(this)] = true;

        _owner = tokenOwner;
        emit Transfer(address(0), tokenOwner, _tTotal);
    }


    function name() public view returns (string memory) {
        return _name;
    }

    function symbol() public view returns (string memory) {
        return _symbol;
    }

    function decimals() public view returns (uint256) {
        return _decimals;
    }
    //总供应量
    function totalSupply() public view override returns (uint256) {
        return _tTotal;
    }

    //余额
    //帐户
    function balanceOf(address account) public view override returns (uint256) {
        if (_isExcluded[account]) return _tOwned[account];
        return tokenFromReflection(_rOwned[account]);
    }

    //转账给
    //接受者 数量
    function transfer(address recipient, uint256 amount) public override returns (bool) {
        _transfer(_msgSender(), recipient, amount);
        return true;
    }

    //批准数量
    //所有者 捐赠者
    function allowance(address owner, address spender) public view override returns (uint256) {
        return _allowances[owner][spender];
    }

    //批准
    //捐赠者 数量
    function approve(address spender, uint256 amount) public override returns (bool) {
        _approve(_msgSender(), spender, amount);
        return true;
    }

    //某人转账给
    //发件人 接受者 数量
    function transferFrom(address sender, address recipient, uint256 amount) public override returns (bool) {
        _transfer(sender, recipient, amount);
        _approve(sender, _msgSender(), _allowances[sender][_msgSender()].sub(amount, "ERC20: transfer amount exceeds allowance"));
        return true;
    }

    //增加批准数量
    // 捐赠者 附加价值
    function increaseAllowance(address spender, uint256 addedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].add(addedValue));
        return true;
    }

    //减少批准数量
    //捐赠者 减去值
    function decreaseAllowance(address spender, uint256 subtractedValue) public virtual returns (bool) {
        _approve(_msgSender(), spender, _allowances[_msgSender()][spender].sub(subtractedValue, "ERC20: decreased allowance below zero"));
        return true;
    }

    //被排除在奖励之外
    //帐户
    function isExcludedFromReward(address account) public view returns (bool) {
        return _isExcluded[account];
    }

    //总费用
    function totalFees() public view returns (uint256) {
        return _tFeeTotal;
    }

    //交付
    //t金额
    function deliver(uint256 tAmount) public {
        address sender = _msgSender();
        //排除的地址无法调用此函数
        //如果 当前合约调用者 不是 _被排除， 否则：排除的地址无法调用此函数
        require(!_isExcluded[sender], "Excluded addresses cannot call this function");
        //r金额 = _获取值
        (uint256 rAmount,,,,,) = _getValues(tAmount);
        //_r拥有[当前合约调用者] = _r拥有[当前合约调用者] - r金额
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        //_r总计 = _r总计 - r金额
        _rTotal = _rTotal.sub(rAmount);
        //_t总费用 = _t总费用 + r金额
        _tFeeTotal = _tFeeTotal.add(tAmount);
    }

    //来自令牌的反射
    //t金额 扣除转会费
    function reflectionFromToken(uint256 tAmount, bool deductTransferFee) public view returns (uint256) {
        //如果 t金额 <= _r总计 , 否则：金额必须少于供应量
        require(tAmount <= _tTotal, "Amount must be less than supply");
        // 不是 扣除转会费
        if (!deductTransferFee) {
            //r金额 = _获取值
            (uint256 rAmount,,,,,) = _getValues(tAmount);
            //返回 r金额
            return rAmount;
            //是 扣除转会费
        } else {
            //r转账金额 = _获取值
            (,uint256 rTransferAmount,,,,) = _getValues(tAmount);
            //返回 r转账金额
            return rTransferAmount;
        }
    }

    //来自反射的令牌
    //r金额
    function tokenFromReflection(uint256 rAmount) public view returns (uint256) {
        //如果 r金额 <= _r 总计 , 否则：数量必须小于全反射
        require(rAmount <= _rTotal, "Amount must be less than total reflections");
        //当前利率 = _获取速率
        uint256 currentRate = _getRate();
        //返回 r金额 / 当前利率
        return rAmount.div(currentRate);
    }

    //从奖励中排除
    //帐户
    function excludeFromReward(address account) public onlyOwner() {
        // require(account != 0x7a250d5630B4cF539739dF2C5dAcb4c659F2488D, 'We can not exclude Uniswap router.');
        //如果 帐户 不是 _被排除，否则：帐户已被排除
        require(!_isExcluded[account], "Account is already excluded");
        //如果  账户 _r拥有 大于 0
        if (_rOwned[account] > 0) {
            //账户 _t拥有 = 来自反射的令牌(账户 _r拥有)
            _tOwned[account] = tokenFromReflection(_rOwned[account]);
        }
        //账户 _被排除 = true
        _isExcluded[account] = true;
        //_排除 添加 账户
        _excluded.push(account);
    }

    //包括在奖励中
    //帐户
    function includeInReward(address account) external onlyOwner() {
        //帐户 _被排除，否则：帐户已被排除
        require(_isExcluded[account], "Account is already excluded");
        //循环 _排除长度
        for (uint256 i = 0; i < _excluded.length; i++) {
            //如果 i _排除 = 账户
            if (_excluded[i] == account) {
                // i _排除 = _排除长度 - 1 _排除
                _excluded[i] = _excluded[_excluded.length - 1];
                //账户 _t拥有 = 0
                _tOwned[account] = 0;
                // 账户 _是排除 = false
                _isExcluded[account] = false;
                //_排除 减少长度
                _excluded.pop();
                //停止循环
                break;
            }
        }
    }

    //_转账两者都排除
    //发件人 接受者 t金额
    function _transferBothExcluded(address sender, address recipient, uint256 tAmount) private {
        //r金额,r转账金额,r费用,t转账金额,t费用,t流动性 = _获取值
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getValues(tAmount);
        //发件人 _t拥有 = 发件人 _t拥有 - t金额
        _tOwned[sender] = _tOwned[sender].sub(tAmount);
        //发件人 _r拥有 = 发件人 _r拥有 - r金额
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        //接受者 _t拥有 = 接受者 _t拥有 + t转账金额
        _tOwned[recipient] = _tOwned[recipient].add(tTransferAmount);
        //接受者 _r拥有 = 接受者 _r拥有 + r转账金额
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        //_取流动性(t流动性)
        _takeLiquidity(tLiquidity);
        //_反映费用(r费用，t费用)
        _reflectFee(rFee, tFee);
        //触发转账事件(发件人，接受者，t转账金额)
        emit Transfer(sender, recipient, tTransferAmount);
    }

    //从费用中排除
    //帐户
    function excludeFromFee(address account) public onlyOwner {
        //账户 _被排除在费用之外 = true
        _isExcludedFromFee[account] = true;
    }

    //包括费用
    //帐户
    function includeInFee(address account) public onlyOwner {
        //账户 _是排除 = false
        _isExcludedFromFee[account] = false;
    }

    //设置税费百分比
    //税费
    function setTaxFeePercent(uint256 taxFee) external onlyOwner() {
        //_税费 = 税费
        _taxFee = taxFee;
    }

    //设置流动性费用百分比
    //流动性费
    function setLiquidityFeePercent(uint256 liquidityFee) external onlyOwner() {
        //_流动资金费 = 流动性费
        _liquidityFee = liquidityFee;
    }

    //设置Num代币出售以增加流动性
    //交换号码
    function setNumTokensSellToAddToLiquidity(uint256 swapNumber) public onlyOwner {
        //出售num代币以增加流动性 = 交换号码 * 10 ** _小数点
        numTokensSellToAddToLiquidity = swapNumber * 10 ** _decimals;
    }

    //设置最大Tx百分比
    //最大Tx百分比
    function setMaxTxPercent(uint256 maxTxPercent) public onlyOwner {
        //_max交易金额 = 最大Tx百分比 * 10 **  _小数点
        _maxTxAmount = maxTxPercent * 10 ** _decimals;
    }

    //设置交换和液化启用
    //_启用
    function setSwapAndLiquifyEnabled(bool _enabled) public onlyOwner {
        //交换和液化启用 = _启用
        swapAndLiquifyEnabled = _enabled;
        //触发 交换和液化已启用更新 事件(_启用)
        emit SwapAndLiquifyEnabledUpdated(_enabled);
    }

    //to recieve ETH from uniswapV2Router when swaping
    //交换时从 uniswapV2Router 接收 ETH
    receive() external payable {}

    //_反映费用
    // r费用 t费用
    function _reflectFee(uint256 rFee, uint256 tFee) private {
        //_r总计 = _r总计 - r费用
        _rTotal = _rTotal.sub(rFee);
        //_t总费用 = _t总费用 + t费用
        _tFeeTotal = _tFeeTotal.add(tFee);
    }

    //_获取值
    //t金额
    function _getValues(uint256 tAmount) private view returns (uint256, uint256, uint256, uint256, uint256, uint256) {
        //_获取T值
        (uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getTValues(tAmount);
        //_获取R值
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee) = _getRValues(tAmount, tFee, tLiquidity, _getRate());
        //返回(t金额,r转账金额,r费用,t转账金额,t费用,t流动性)
        return (rAmount, rTransferAmount, rFee, tTransferAmount, tFee, tLiquidity);
    }

    //获取T值
    //t金额
    function _getTValues(uint256 tAmount) private view returns (uint256, uint256, uint256) {
        //t费用 = 计算税费
        uint256 tFee = calculateTaxFee(tAmount);
        //t流动性 = 计算流动性费用
        uint256 tLiquidity = calculateLiquidityFee(tAmount);
        //t转账金额 = t金额 - t费用 - t流动性
        uint256 tTransferAmount = tAmount.sub(tFee).sub(tLiquidity);
        //返回(t转账金额，t费用，t流动性)
        return (tTransferAmount, tFee, tLiquidity);
    }

    //_获取R值
    //t金额 t费用 t费用 t流动性 当前利率
    function _getRValues(uint256 tAmount, uint256 tFee, uint256 tLiquidity, uint256 currentRate) private pure returns (uint256, uint256, uint256) {
        //r金额 = t金额 * 当前利率
        uint256 rAmount = tAmount.mul(currentRate);
        //r费用 = t费用 * 当前利率
        uint256 rFee = tFee.mul(currentRate);
        //r流动性 = 流动性 * 当前利率
        uint256 rLiquidity = tLiquidity.mul(currentRate);
        //r转账金额 = r金额 - r费用 - r流动性
        uint256 rTransferAmount = rAmount.sub(rFee).sub(rLiquidity);
        //返回 (r金额,r转账金额,r费用)
        return (rAmount, rTransferAmount, rFee);
    }

    //_获取速率
    function _getRate() private view returns (uint256) {
        //r供应，t供应 = _排除
        (uint256 rSupply, uint256 tSupply) = _getCurrentSupply();
        // 返回 r供应 / t供应
        return rSupply.div(tSupply);
    }

    //_获取当前供应
    function _getCurrentSupply() private view returns (uint256, uint256) {
        //r供应 = _r总计
        uint256 rSupply = _rTotal;
        //t供应 = _t总计
        uint256 tSupply = _tTotal;
        //循环 _排除 数组
        for (uint256 i = 0; i < _excluded.length; i++) {
            //如果 _r拥有[_排除[i]]>r供应 或者 _t拥有[_排除[i]] > t供应 返回 _r供应 _t供应
            if (_rOwned[_excluded[i]] > rSupply || _tOwned[_excluded[i]] > tSupply) return (_rTotal, _tTotal);
            //r供应 = r供应 - _r拥有[_排除[i]]
            rSupply = rSupply.sub(_rOwned[_excluded[i]]);
            //t供应 = t供应 - _t拥有[_排除[i]]
            tSupply = tSupply.sub(_tOwned[_excluded[i]]);
        }
        //如果 r供应 <_r总计 /_t总计 返回_r总计，_t总计
        if (rSupply < _rTotal.div(_tTotal)) return (_rTotal, _tTotal);
        //返回 (r供应，t供应)
        return (rSupply, tSupply);
    }

    //_取流动性
    //t流动性
    function _takeLiquidity(uint256 tLiquidity) private {
        //当前利率 = _获取速率
        uint256 currentRate = _getRate();
        //r流动性 = t流动性 *　当前利率
        uint256 rLiquidity = tLiquidity.mul(currentRate);
        //当前合约 _r拥有者 = 当前合约 _r拥有者 +　r流动性
        _rOwned[address(this)] = _rOwned[address(this)].add(rLiquidity);
        //如果 当前合约 _是排除
        if (_isExcluded[address(this)])
        //当前合约 _t拥有者 = 当前合约 _t拥有者 + t流动性
            _tOwned[address(this)] = _tOwned[address(this)].add(tLiquidity);
    }

    //索取代币
    function claimTokens() public onlyOwner {
        payable(_owner).transfer(address(this).balance);
    }
    //计算税费
    //_数量
    function calculateTaxFee(uint256 _amount) private view returns (uint256) {
        //_数量 * 税费 / 100
        return _amount.mul(_taxFee).div(10 ** 2);
    }

    //计算流动性费用
    //_数量
    function calculateLiquidityFee(uint256 _amount) private view returns (uint256) {
        //_数量 * _流动资金费 / 100
        return _amount.mul(_liquidityFee).div(10 ** 2);
    }

    //删除所有费用
    function removeAllFee() private {
        //如果 _税费 == 0 与 _流动资金费 ==0 返回
        if (_taxFee == 0 && _liquidityFee == 0) return;

        //_以前的税费 = _税费
        _previousTaxFee = _taxFee;
        //_先前的流动资金费用 = _流动资金费
        _previousLiquidityFee = _liquidityFee;

        //_税费 = 0
        _taxFee = 0;
        //_流动资金费 = 0
        _liquidityFee = 0;
    }

    //恢复所有费用
    function restoreAllFee() private {
        //_税费 = _以前的税费
        _taxFee = _previousTaxFee;
        //_流动资金费 = _先前的流动资金费用
        _liquidityFee = _previousLiquidityFee;
    }

    //不收费
    //帐户
    function isExcludedFromFee(address account) public view returns (bool) {
        //账户 _被排除在费用之外
        return _isExcludedFromFee[account];
    }

    //_批准
    // 所有者 捐赠者 数量
    function _approve(address owner, address spender, uint256 amount) private {
        //如果 所有者 != 空地址 ，否则：从零地址批准
        require(owner != address(0), "ERC20: approve from the zero address");
        //如果 捐赠者 != 空地址 否则：同意零地址
        require(spender != address(0), "ERC20: approve to the zero address");

        //所有者 捐赠者 _津贴 = 数量
        _allowances[owner][spender] = amount;
        //触发 批准事件(所有者,捐赠者，数量)
        emit Approval(owner, spender, amount);
    }

    //_转账
    //从 至 数量
    function _transfer(address from, address to, uint256 amount) private {
        //如果 从 != 空地址 否则：从零地址转账
        require(from != address(0), "ERC20: transfer from the zero address");
        //如果 至 != 空地址 否则：转移到零地址
        require(to != address(0), "ERC20: transfer to the zero address");
        // 如果 数量 > 0 否则：转账金额必须大于零
        require(amount > 0, "Transfer amount must be greater than zero");
        //如果 从 != 所有者 与 至 != 所有者
        if (from != owner() && to != owner())
        //如果 数量 <= _max交易金额 否则：转账金额超过max交易金额
            require(amount <= _maxTxAmount, "Transfer amount exceeds the maxTxAmount.");

        // is the token balance of this contract address over the min number of 是这个合约地址的代币余额超过最小数量
        // tokens that we need to initiate a swap + liquidity lock? 我们需要启动掉期+流动性锁定的代币？
        // also, don't get caught in a circular liquidity event. 另外，不要陷入循环流动性事件中。
        // also, don't swap & liquify if sender is uniswap pair. 另外，如果发件人是单交换对，则不要交换和液化。
        // 合约代币余额 = 余额(当前合约)
        uint256 contractTokenBalance = balanceOf(address(this));
        //如果 合约代币余额 >= _max交易金额
        if (contractTokenBalance >= _maxTxAmount) {
            //合约代币余额 = _max交易金额
            contractTokenBalance = _maxTxAmount;
        }

        //超过最小代币余额 = 合约代币余额 >= 出售 num 代币以增加流动性
        bool overMinTokenBalance = contractTokenBalance >= numTokensSellToAddToLiquidity;
        //如果 超过最小代币余额 && !在交换和液化 && 从 != uniswapV2Pair && 交换和液化启用
        if (
            overMinTokenBalance &&
            !inSwapAndLiquify &&
            from != uniswapV2Pair &&
            swapAndLiquifyEnabled
        ) {
            //合约代币余额 = 出售num代币以增加流动性
            contractTokenBalance = numTokensSellToAddToLiquidity;
            //add liquidity
            //增加流动性
            swapAndLiquify(contractTokenBalance);
        }

        //indicates if fee should be deducted from transfer
        bool takeFee = true;

        //if any account belongs to _isExcludedFromFee account then remove the fee
        if (_isExcludedFromFee[from] || _isExcludedFromFee[to]) {
            takeFee = false;
        }

        //transfer amount, it will take tax, burn, liquidity fee
        _tokenTransfer(from, to, amount, takeFee);
    }

    //交换和液化
    //合约代币余额
    function swapAndLiquify(uint256 contractTokenBalance) private lockTheSwap {
        // split the contract balance into halves 将合约余额分成两半
        // 一半 = 合约代币余额 / 2
        uint256 half = contractTokenBalance.div(2);
        // 另一半 = 合约代币余额 - 一半
        uint256 otherHalf = contractTokenBalance.sub(half);

        // capture the contract's current ETH balance. 获取合约当前的 ETH 余额
        // this is so that we can capture exactly the amount of ETH that the 这样我们就可以准确地捕捉到 ETH 的数量
        // swap creates, and not make the liquidity event include any ETH that 掉期创建，而不是使流动性事件包括任何 ETH
        // has been manually sent to the contract 已经手动发送到合约
        //初始余额 = 当前合约 . 余额
        uint256 initialBalance = address(this).balance;

        // swap tokens for ETH 将代币换成 ETH

        swapTokensForEth(half);
        // <- this breaks the ETH -> HATE swap when swap+liquify is triggered

        // how much ETH did we just swap into?
        uint256 newBalance = address(this).balance.sub(initialBalance);

        // add liquidity to uniswap
        addLiquidity(otherHalf, newBalance);

        emit SwapAndLiquify(half, newBalance, otherHalf);
    }

    //将代币换成 Eth
    //代币数量
    function swapTokensForEth(uint256 tokenAmount) private {
        // generate the uniswap pair path of token -> weth 生成 token -> weth 的 Uniswap 对路径
        // 小路 = 两位空地址
        address[] memory path = new address[](2);
        //小路0 = 当前合约
        path[0] = address(this);
        //小路1 = uniswapV2Router.WETH();
        path[1] = uniswapV2Router.WETH();

        //_批准(当前合约，address(uniswapV2Router),代币数量)
        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // make the swap  进行交换
        //uniswapV2Router.将确切代币换成 ETH 转账代币支持费(代币数量,0,小路,当前合约.区块时间戳)
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0, // accept any amount of ETH
            path,
            address(this),
            block.timestamp
        );
    }

    //增加流动性
    //代币数量 以太币数量
    function addLiquidity(uint256 tokenAmount, uint256 ethAmount) private {
        // approve token transfer to cover all possible scenarios 批准令牌转移以涵盖所有可能的情况
        //_批准(当前合约，address(uniswapV2Router),代币数量)
        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // add the liquidity 增加流动性
        // uniswapV2Router.添加流动性 ETH{value:以太币数量}(当前合约，代币数量，0，0，当前合约拥有者，当前区块时间戳)
        uniswapV2Router.addLiquidityETH{value : ethAmount}(
            address(this),
            tokenAmount,
            0, // slippage is unavoidable
            0, // slippage is unavoidable
            owner(),
            block.timestamp
        );
    }

    //this method is responsible for taking all fee, if takeFee is true
    //此方法负责收取所有费用，如果 takeFee 为真
    //_token转账
    //发件人 接受者 数量 收取费用
    function _tokenTransfer(address sender, address recipient, uint256 amount, bool takeFee) private {
        //如果 ！收取费用
        if (!takeFee)
        //删除所有费用
            removeAllFee();
        //如果 发件人 _被排除 与 接受者 _被排除
        if (_isExcluded[sender] && !_isExcluded[recipient]) {
            //_从排除转移(发件人,接受者,数量)
            _transferFromExcluded(sender, recipient, amount);
            //如果 发件人 ! _被排除 与 接受者 发件人
        } else if (!_isExcluded[sender] && _isExcluded[recipient]) {
            //_转移到排除(发件人,接受者,数量)
            _transferToExcluded(sender, recipient, amount);
            //如果 发件人 ! _被排除 与 接受者 ! _被排除
        } else if (!_isExcluded[sender] && !_isExcluded[recipient]) {
            //_转移标准(发件人,接受者,数量)
            _transferStandard(sender, recipient, amount);
            //如果 发件人 _被排除 与 接受者 _被排除
        } else if (_isExcluded[sender] && _isExcluded[recipient]) {
            //_转账两者都排除(发件人,接受者,数量)
            _transferBothExcluded(sender, recipient, amount);
            //否则
        } else {
            //_转移标准(发件人,接受者,数量)
            _transferStandard(sender, recipient, amount);
        }

        //如果 !收取费用
        if (!takeFee)
        //恢复所有费用
            restoreAllFee();
    }

    //_转移标准
    //发件人 接受者 t金额
    function _transferStandard(address sender, address recipient, uint256 tAmount) private {
        //r金额,r转账金额,r费用,t转账金额,t费用,t流动性 = _获取值(t金额)
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getValues(tAmount);
        //发件人 _r拥有 = 发件人 _r拥有 - r金额
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        //接受者 _r拥有 = 接受者 _r拥有 + r转账金额
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        //_取流动性(t流动性)
        _takeLiquidity(tLiquidity);
        //_反映费用(r费用,t费用)
        _reflectFee(rFee, tFee);
        //触发 转账事件(发件人,接受者,t转账金额)
        emit Transfer(sender, recipient, tTransferAmount);
    }

    //_转移到排除
    // 发件人 接受者 t金额
    function _transferToExcluded(address sender, address recipient, uint256 tAmount) private {
        //r金额，r转账金额，r费用，t转账金额，t费用，t流动性 = _获取值(t金额)
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getValues(tAmount);
        //发件人 _r拥有 = 发件人 _r拥有 - r金额
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        //接受者 _t拥有 = 接受者 _t拥有 + t转账金额
        _tOwned[recipient] = _tOwned[recipient].add(tTransferAmount);
        //接受者 _r拥有 = 接受者 _r拥有 + r转账金额
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        //_取流动性(t流动性)
        _takeLiquidity(tLiquidity);
        //_反映费用(r费用,t费用)
        _reflectFee(rFee, tFee);
        //触发 转账事件(发件人,接受者,t转账金额)
        emit Transfer(sender, recipient, tTransferAmount);
    }

    //_从排除转移
    //发件人 接受者 t金额
    function _transferFromExcluded(address sender, address recipient, uint256 tAmount) private {
        // r金额,r转账金额,r费用,t转账金额,t费用,t流动性 = _获取值(t金额)
        (uint256 rAmount, uint256 rTransferAmount, uint256 rFee, uint256 tTransferAmount, uint256 tFee, uint256 tLiquidity) = _getValues(tAmount);
        //发件人 _t拥有 = 发件人 _t拥有 - t金额
        _tOwned[sender] = _tOwned[sender].sub(tAmount);
        //发件人 _r拥有 = 发件人 _r拥有 - r金额
        _rOwned[sender] = _rOwned[sender].sub(rAmount);
        //接受者 _r拥有 = 接受者 _r拥有 + r转账金额
        _rOwned[recipient] = _rOwned[recipient].add(rTransferAmount);
        //_拿流动性(t流动性)
        _takeLiquidity(tLiquidity);
        //反映费(r费用,t费用)
        _reflectFee(rFee, tFee);
        //触发 转账事件(发件人,接受者,t转账金额)
        emit Transfer(sender, recipient, tTransferAmount);
    }
}
