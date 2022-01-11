// Copyright 2017 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package vm

import (
	"encoding/json"
	"errors"
	"fmt"
	"github.com/ethereum/go-ethereum/common/hexutil"
	"github.com/ethereum/go-ethereum/core/types"
	"math/big"
	"os"
	"path"
	"strconv"
	"strings"
	"time"

	"github.com/ethereum/go-ethereum/common"
)

func getFile(taskName string, blockNumber uint64, perFolder, perFile uint64) (*os.File, error) {
	cwd, err := os.Getwd()
	if err != nil {
		return nil, fmt.Errorf("get current work dir failed: %w", err)
	}

	logPath := path.Join(cwd, taskName, strconv.FormatUint(blockNumber/perFolder, 10), strconv.FormatUint(blockNumber/perFile, 10)+".log")
	fmt.Printf("log path: %v, block: %v\n", logPath, blockNumber)
	if err := os.MkdirAll(path.Dir(logPath), 0755); err != nil {
		return nil, fmt.Errorf("mkdir for all parents [%v] failed: %w", path.Dir(logPath), err)
	}

	file, err := os.OpenFile(logPath, os.O_APPEND|os.O_CREATE|os.O_WRONLY, 0755)
	if err != nil {
		return nil, fmt.Errorf("create file %s failed: %w", logPath, err)
	}
	return file, nil
}

type ParityTraceItemAction struct {
	CallType string         `json:"callType"`
	From     common.Address `json:"from"`
	To       common.Address `json:"to"`
	Gas      hexutil.Uint64 `json:"gas"`
	Input    hexutil.Bytes  `json:"input"`
	Value    hexutil.Bytes  `json:"value"`
}

type ParityTraceItemResult struct {
	GasUsed hexutil.Uint64 `json:"gasUsed"`
	Output  hexutil.Bytes  `json:"output"`
}

type ParityTraceItem struct {
	Type                 string                `json:"type"`
	Action               ParityTraceItemAction `json:"action"`
	Result               ParityTraceItemResult `json:"result"`
	Subtraces            int                   `json:"subtraces"`
	TraceAddress         []int                 `json:"traceAddress"`
	Error                string                `json:"error,omitempty"`
	BlockHash            common.Hash           `json:"blockHash"`
	BlockNumber          uint64                `json:"blockNumber"`
	TransactionHash      common.Hash           `json:"transactionHash"`
	TransactionPosition  int                   `json:"transactionPosition"`
	TransactionTraceID   int                   `json:"transactionTraceID"`
	TransactionLastTrace int                   `json:"transactionLastTrace"`

	outOff  int64
	outLen  int64
	gasIn   uint64
	gasCost uint64
}

type ParityLogContext struct {
	BlockHash   common.Hash
	BlockNumber uint64
	TxPos       int
	TxHash      common.Hash
}

type ParityLogger struct {
	context           *ParityLogContext
	sb                *strings.Builder
	encoder           *json.Encoder
	activePrecompiles []common.Address
	file              *os.File
	stack             []*ParityTraceItem
	items             []*ParityTraceItem
	err               error
	descended         bool
}

// NewParityLogger creates a new EVM tracer that prints execution steps as parity trace format
// into the provided stream.
func NewParityLogger(ctx *ParityLogContext, blockNumber uint64, perFolder, perFile uint64) (*ParityLogger, error) {
	file, err := getFile("traces", blockNumber, perFolder, perFile)
	if err != nil {
		return nil, err
	}
	sb := &strings.Builder{}
	l := &ParityLogger{context: ctx, sb: sb, encoder: json.NewEncoder(sb), file: file}
	if l.context == nil {
		l.context = &ParityLogContext{}
	}
	return l, nil
}

func (l *ParityLogger) Close() error {
	if _, err := l.file.WriteString(l.sb.String()); err != nil {
		return err
	}
	return l.file.Close()
}

func (l *ParityLogger) CaptureStart(env *EVM, from, to common.Address, create bool, input []byte, gas uint64, value *big.Int) {
	rules := env.ChainConfig().Rules(env.Context.BlockNumber)
	l.activePrecompiles = ActivePrecompiles(rules)
	l.stack = make([]*ParityTraceItem, 0, 20)
	l.items = make([]*ParityTraceItem, 0, 20)
	l.err = nil
	l.descended = false
	if create {
		l.captureEnter(CREATE, from, to, input, gas, value)
	} else {
		l.captureEnter(CALL, from, to, input, gas, value)
	}
}

func (l *ParityLogger) CaptureFault(evm *EVM, pc uint64, op OpCode, gas uint64, cost uint64, scope *ScopeContext, depth int, err error) {
	size := len(l.stack)
	l.captureExit([]byte{}, uint64(l.stack[size-1].Action.Gas)-gas, err)
}

// CaptureState outputs state information on the logger.
func (l *ParityLogger) CaptureState(env *EVM, pc uint64, op OpCode, gas, cost uint64, scope *ScopeContext, rData []byte, depth int, err error) {
	// Capture any errors immediately
	if err != nil {
		l.CaptureFault(env, pc, op, gas, cost, scope, depth, err)
		return
	}
	// We only care about system opcodes, faster if we pre-check once
	var syscall = (op & 0xf0) == 0xf0

	// If a new contract is being created, add to the call stack
	if syscall && (op == CREATE || op == CREATE2) {
		var inOff = int64(scope.Stack.Back(1).Uint64())
		var inLen = int64(scope.Stack.Back(2).Uint64())
		var value = &big.Int{}
		value.SetString(scope.Stack.Back(0).Hex(), 0)
		l.captureEnter(op, scope.Contract.Address(), common.Address{}, scope.Memory.GetCopy(inOff, inLen), gas, value)
		l.stack[len(l.stack)-1].gasCost = cost

		l.descended = true
		return
	}

	// If a contract is being self destructed, gather that as a subcall too
	if syscall && op == SELFDESTRUCT {
		to := common.HexToAddress(scope.Stack.Back(0).Hex())
		value := env.StateDB.GetBalance(scope.Contract.Address())
		l.captureEnter(op, scope.Contract.Address(), to, []byte{}, gas, value)
		l.captureExit([]byte{}, 0, nil)
		return
	}

	// If a new method invocation is being done, add to the call stack
	if syscall && (op == CALL || op == CALLCODE || op == DELEGATECALL || op == STATICCALL) {
		// Skip any pre-compile invocations, those are just fancy opcodes
		var to = common.HexToAddress(scope.Stack.Back(1).Hex())
		if l.isPrecompiled(to) {
			return
		}
		var off int
		value := &big.Int{}
		if op == DELEGATECALL || op == STATICCALL {
			off = 0
		} else {
			off = 1
			value.SetString(scope.Stack.Back(2).Hex(), 0)
		}

		var inOff = int64(scope.Stack.Back(2 + off).Uint64())
		var inLen = int64(scope.Stack.Back(3 + off).Uint64())

		l.captureEnter(op, scope.Contract.Address(), to, scope.Memory.GetCopy(inOff, inLen), gas, value)
		size := len(l.stack)
		l.stack[size-1].outOff = int64(scope.Stack.Back(4 + off).Uint64())
		l.stack[size-1].outLen = int64(scope.Stack.Back(5 + off).Uint64())
		l.stack[size-1].gasCost = cost

		l.descended = true
		return
	}
	// If we've just descended into an inner call, retrieve it's true allowance. We
	// need to extract if from within the call as there may be funky gas dynamics
	// with regard to requested and actually given gas (2300 stipend, 63/64 rule).
	if l.descended {
		if depth >= len(l.stack) {
			l.stack[len(l.stack)-1].Action.Gas = hexutil.Uint64(gas)
		} else {
			// TODO(karalabe): The call was made to a plain account. We currently don't
			// have access to the true gas amount inside the call and so any amount will
			// mostly be wrong since it depends on a lot of input args. Skip gas for now.
		}
		l.descended = false
	}

	if syscall && op == REVERT {
		return
	}

	// If an existing call is returning, pop off the call stack
	if depth == len(l.stack)-1 {
		// Pop off the last call and get the execution results

		size := len(l.stack)
		callType := l.stack[size-1].Action.CallType
		var (
			err     error
			output  []byte
			gasUsed uint64
		)
		if callType == strings.ToLower(opCodeToString[CREATE]) || callType == strings.ToLower(opCodeToString[CREATE2]) {
			gasUsed = l.stack[size-1].gasIn - l.stack[size-1].gasCost - gas
			ret := scope.Stack.Back(0)
			if !ret.IsZero() {
				addr := common.HexToAddress(ret.Hex())
				l.stack[size-1].Action.To = addr
				output = env.StateDB.GetCode(addr)
			} else {
				err = errors.New("internal failure")
				fmt.Println("internal failure: ret equals zero -- 1")
			}
		} else {
			// If the call was a contract call, retrieve the gas usage and output
			gasUsed = l.stack[size-1].gasIn - l.stack[size-1].gasCost + uint64(l.stack[size-1].Action.Gas) - gas
			ret := scope.Stack.Back(0)
			if !ret.IsZero() {
				output = scope.Memory.GetCopy(l.stack[size-1].outOff, l.stack[size-1].outLen)
			} else {
				err = errors.New("internal failure")
				fmt.Println("internal failure: ret equals zero -- 2")
			}
		}
		l.captureExit(output, gasUsed, err)
	}
}

// CaptureEnd is triggered at end of execution.
func (l *ParityLogger) CaptureEnd(output []byte, gasUsed uint64, t time.Duration, err error) {
	if len(l.stack) > 0 {
		l.captureExit(output, gasUsed, err)
	} else if len(l.items) > 0 && l.items[0].Error == "" && err != nil {
		l.items[0].Error = err.Error()
	}
	if len(l.stack) > 0 {
		fmt.Printf("block: %v, tx: %v, trace end with stack size %v", l.context.BlockNumber, l.context.TxPos, len(l.stack))
	}
	itemsSize := len(l.items)
	for no, item := range l.items {
		item.TransactionTraceID = no
		if no+1 == itemsSize {
			item.TransactionLastTrace = 1
		} else {
			item.TransactionLastTrace = 0
		}
		l.encoder.Encode(item)
	}
}

func getTraceType(typ OpCode) string {
	if typ == CALL || typ == DELEGATECALL || typ == CALLCODE || typ == STATICCALL {
		return "call"
	} else if typ == CREATE || typ == CREATE2 {
		return "create"
	} else if typ == SELFDESTRUCT {
		return "suicide"
	} else {
		return "unknown"
	}
}

func (l *ParityLogger) captureEnter(typ OpCode, from common.Address, to common.Address, input []byte, gas uint64, value *big.Int) {
	traceAddress := make([]int, 0, 5)
	if len(l.stack) > 0 {
		back := l.stack[len(l.stack)-1]
		traceAddress = append(traceAddress, back.TraceAddress...)
		traceAddress = append(traceAddress, back.Subtraces)
		back.Subtraces += 1
	}
	newItem := &ParityTraceItem{
		Type: getTraceType(typ),
		Action: ParityTraceItemAction{
			CallType: strings.ToLower(typ.String()),
			From:     from,
			To:       to,
			Gas:      hexutil.Uint64(gas),
			Input:    append([]byte{}, input...),
		},
		Result: ParityTraceItemResult{
			GasUsed: 0,
			Output:  nil,
		},
		Subtraces:           0,
		TraceAddress:        traceAddress,
		BlockHash:           l.context.BlockHash,
		BlockNumber:         l.context.BlockNumber,
		TransactionHash:     l.context.TxHash,
		TransactionPosition: l.context.TxPos,

		gasIn: gas,
	}
	if value != nil {
		newItem.Action.Value = value.Bytes()
	}

	l.items = append(l.items, newItem)
	l.stack = append(l.stack, newItem)
}

func (l *ParityLogger) isPrecompiled(addr common.Address) bool {
	for _, p := range l.activePrecompiles {
		if p == addr {
			return true
		}
	}
	return false
}

func (l *ParityLogger) captureExit(output []byte, gasUsed uint64, err error) {
	current := l.stack[len(l.stack)-1]
	current.Result.GasUsed = hexutil.Uint64(gasUsed)
	current.Result.Output = append([]byte{}, output...)
	if err != nil {
		current.Error += err.Error()
	}
	l.stack = l.stack[0 : len(l.stack)-1]

	// remove precompiled call
	if l.isPrecompiled(current.Action.To) {
		s := len(l.items)
		l.items = l.items[0 : s-1]
		if s > 1 {
			l.items[s-2].Subtraces -= 1
		}
	}
}

func ReceiptDumpLogger(blockNumber uint64, perFolder, perFile uint64, receipts types.Receipts) error {
	file, err := getFile("receipts", blockNumber, perFolder, perFile)
	if err != nil {
		return err
	}

	sb := &strings.Builder{}
	encoder := json.NewEncoder(sb)
	for _, receipt := range receipts {
		for _, log := range receipt.Logs {
			err := encoder.Encode(log)
			if err != nil {
				return fmt.Errorf("encode log failed: %w", err)
			}
		}
	}
	if _, err := file.WriteString(sb.String()); err != nil {
		return err
	}
	return nil
}

type TxLogger struct {
	blockNumber uint64
	blockHash   common.Hash
	sb          *strings.Builder
	file        *os.File
	encoder     *json.Encoder
	signer      types.Signer
}

func NewTxLogger(signer types.Signer, blockHash common.Hash, blockNumber uint64, perFolder, perFile uint64) (*TxLogger, error) {
	file, err := getFile("transactions", blockNumber, perFolder, perFile)
	if err != nil {
		return nil, err
	}
	sb := &strings.Builder{}
	return &TxLogger{
		blockNumber: blockNumber,
		blockHash:   blockHash,
		file:        file,
		sb:          sb,
		encoder:     json.NewEncoder(sb),
		signer:      signer,
	}, nil
}

func (t *TxLogger) Dump(index int, tx *types.Transaction, receipt *types.Receipt) error {
	from, _ := types.Sender(t.signer, tx)
	// Assign the effective gas price paid
	//effectiveGasPrice := hexutil.Uint64(tx.GasPrice().Uint64())
	//if t.isLondon {
	//	gasPrice := new(big.Int).Add(t.baseFee, tx.EffectiveGasTipValue(t.baseFee))
	//	effectiveGasPrice = hexutil.Uint64(gasPrice.Uint64())
	//}
	entry := map[string]interface{}{
		"blockNumber":      t.blockNumber,
		"blockHash":        t.blockHash,
		"transactionIndex": index,
		"transactionHash":  tx.Hash(),
		"from":             from,
		"to":               tx.To(),
		"gas":              tx.Gas(),
		"gasUsed":          receipt.GasUsed,
		"gasPrice":         tx.GasPrice(),
		"data":             tx.Data(),
		"accessList":       tx.AccessList(),
		"nonce":            tx.Nonce(),
		//"gasFeeCap":         tx.GasFeeCap(),
		//"gasTipCap":         tx.GasTipCap(),
		//"effectiveGasPrice": effectiveGasPrice,
		"type":   tx.Type(),
		"value":  tx.Value(),
		"status": receipt.Status,
	}
	if err := t.encoder.Encode(entry); err != nil {
		return fmt.Errorf("failed to encode transaction entry %w", err)
	}
	return nil
}

func (t *TxLogger) Close() error {
	if _, err := t.file.WriteString(t.sb.String()); err != nil {
		return err
	}
	return t.file.Close()
}

func BlockDumpLogger(block *types.Block, perFolder, perFile uint64) error {
	file, err := getFile("blocks", block.NumberU64(), perFolder, perFile)
	if err != nil {
		return err
	}
	defer file.Close()

	entry := map[string]interface{}{
		"timestamp":   block.Time(),
		"blockNumber": block.NumberU64(),
		"blockHash":   block.Hash(),
		"parentHash":  block.ParentHash(),
		"gasLimit":    block.GasLimit(),
		"gasUsed":     block.GasUsed(),
		"miner":       block.Coinbase(),
		"difficulty":  block.Difficulty(),
		"nonce":       block.Nonce(),
		"size":        block.Size(),
	}
	encoder := json.NewEncoder(file)
	if err := encoder.Encode(entry); err != nil {
		return fmt.Errorf("failed to encode transaction entry %w", err)
	}

	return nil
}
