// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/block"
	"cmd/compile/internal/ssa/ssaop"
)

// fuseBounds runs after prove has used the original guard chain to eliminate
// downstream checks. It combines two adjacent bounds guards into one hot-path
// guard, preserving the original panic dispatch on a cold path.
//
// The arithmetic matcher handles both:
//
//	0 <= i <= n; 0 <= k < n-i    -> 0 <= i+k < n
//	0 <= i < n;  0 <= i+k < n    -> 0 <= i+k < n
//
// and their inclusive variants, when addition cannot wrap unsigned. Bounds values
// are compiler-generated nonnegative limits, as required by Is[Slice]InBounds.
// Signed overflow is harmless: the unsigned end check fails for negative ends.
// A candidate's maximum is captured before either guard succeeds. Facts from
// the later guard must never justify arithmetic moved before the first guard.
type boundsCandidate struct {
	block   *ssa.Block
	guard   *ssa.Value
	maximum uint64
}

func fuseBounds(f *ssa.Func, candidates []boundsCandidate) {
	for _, candidate := range candidates {
		b := candidate.block
		if !boundsGuard(b) || b.Controls[0] != candidate.guard {
			continue
		}
		first := b.Controls[0]
		i, n := first.Args[0], first.Args[1]
		word := i.Type.Size()
		if word != 4 && word != 8 {
			continue
		}
		window := b.Succs[0].B
		if !boundsGuard(window) || len(window.Preds) != 1 || !boundsPure(window) {
			continue
		}
		second := window.Controls[0]
		index, limit := second.Args[0], second.Args[1]
		var k int64
		remaining := boundsScalar(limit)
		shifted := false
		if boundsDifference(remaining, n, i) && boundsConst(index, word) {
			k = index.AuxInt
		} else if limit == n {
			ibase, idelta := boundsDelta(i)
			jbase, jdelta := boundsDelta(index)
			if ibase != jbase {
				continue
			}
			k, shifted = jdelta-idelta, true
			if word == 4 {
				k = int64(int32(k))
			}
		} else {
			continue
		}
		if k < 0 || unsignedAddOverflows(candidate.maximum, uint64(k), i.Type) {
			continue
		}
		if first.Op == ssaop.OpIsInBounds && second.Op == ssaop.OpIsSliceInBounds && k == 0 {
			continue // an inclusive end check would not imply the first strict check
		}
		p1block, p2block := b.Succs[1].B, window.Succs[1].B
		p1, p2 := boundsPanic(p1block), boundsPanic(p2block)
		if p1 == nil || p2 == nil || p1.Args[0] != i || p1.Args[1] != n ||
			p2.Args[0] != index || p2.Args[1] != limit || p1.Args[2] != p2.Args[2] {
			continue
		}

		constantOp, addOp, subOp := ssaop.OpConst64, ssaop.OpAdd64, ssaop.OpSub64
		if word == 4 {
			constantOp, addOp, subOp = ssaop.OpConst32, ssaop.OpAdd32, ssaop.OpSub32
		}
		offset := b.NewValue0I(second.Pos, constantOp, i.Type, k)
		end := b.NewValue2(second.Pos, addOp, i.Type, i, offset)
		b.SetControl(b.NewValue2(second.Pos, second.Op, first.Type, end, n))
		b.Likely = ssa.BranchLikely

		// Slice-specific cleanup is optional; fusion itself is scalar.
		// Both strict and inclusive end guards imply a nonempty suffix
		// when k > 0; a strict guard also does so when k == 0.
		if k > 0 || second.Op == ssaop.OpIsInBounds {
			boundsRemoveMasks(window, i, n)
		}

		if shifted {
			p2.SetArg(0, end)
		} else {
			p2.SetArg(0, p2block.NewValue0I(index.Pos, constantOp, index.Type, k))
			p2.SetArg(1, p2block.NewValue2(limit.Pos, subOp, n.Type, n, i))
		}
		slow := f.NewBlock(block.BlockIf)
		slow.Pos = b.Pos
		slow.SetControl(first)
		slow.Likely = ssa.BranchLikely
		p1block.RemovePred(b.Succs[1].I)
		b.RemoveSucc(1)
		p2block.RemovePred(window.Succs[1].I)
		window.RemoveSucc(1)
		window.Reset(block.BlockPlain)
		window.Likely = ssa.BranchUnknown
		b.AddEdgeTo(slow)
		slow.AddEdgeTo(p2block)
		slow.AddEdgeTo(p1block)
		if f.Pass.Debug > 0 {
			f.Warnl(second.Pos, "Fused bounds checks")
		}
	}
}

func boundsGuard(b *ssa.Block) bool {
	return b.Kind == block.BlockIf && (b.Controls[0].Op == ssaop.OpIsInBounds || b.Controls[0].Op == ssaop.OpIsSliceInBounds)
}

// Peel the aggregate accessor without changing its length or capacity.
// No SliceMake is required when the checks already refer to scalar values.
func boundsScalar(v *ssa.Value) *ssa.Value {
	if v.Op == ssaop.OpSliceLen && v.Args[0].Op == ssaop.OpSliceMake || v.Op == ssaop.OpStringLen && v.Args[0].Op == ssaop.OpStringMake {
		return v.Args[0].Args[1]
	}
	return v
}

func boundsConst(v *ssa.Value, word int64) bool {
	return word == 8 && v.Op == ssaop.OpConst64 || word == 4 && v.Op == ssaop.OpConst32
}

func boundsSub(v *ssa.Value, word int64) bool {
	return word == 8 && v.Op == ssaop.OpSub64 || word == 4 && v.Op == ssaop.OpSub32
}

// Match n-i even after constant reassociation, for example
// n-(a+16) -> (n-a)-16. These identities hold modulo the word size.
func boundsDifference(v, n, i *ssa.Value) bool {
	word := i.Type.Size()
	base, delta := boundsDelta(v)
	nbase, ndelta := boundsDelta(n)
	ibase, idelta := boundsDelta(i)
	want := ndelta - idelta
	if word == 4 {
		want = int64(int32(want))
	}
	return boundsSub(base, word) && base.Args[0] == nbase && base.Args[1] == ibase && delta == want
}

func boundsDelta(v *ssa.Value) (*ssa.Value, int64) {
	var delta int64
	word := v.Type.Size()
	for count := 0; count < 64; count++ {
		base, d := isConstDelta(v)
		if base == nil {
			break
		}
		delta += d
		if word == 4 {
			delta = int64(int32(delta))
		}
		v = base
	}
	return v, delta
}

func boundsRemoveMasks(b *ssa.Block, i, n *ssa.Value) {
	for _, v := range b.Values {
		if v.Op != ssaop.OpSlicemask {
			continue
		}
		if !boundsDifference(v.Args[0], n, i) {
			base, _ := boundsDelta(v.Args[0])
			if !boundsSub(base, i.Type.Size()) {
				continue
			}
			capacity := base.Args[0]
			if n.Op != ssaop.OpSliceLen || capacity.Op != ssaop.OpSliceCap || n.Args[0] != capacity.Args[0] || !boundsDifference(v.Args[0], capacity, i) {
				continue
			}
		}
		if v.Type.Size() == 8 {
			v.Reset(ssaop.OpConst64)
		} else {
			v.Reset(ssaop.OpConst32)
		}
		v.AuxInt = -1
	}
}

func boundsPanic(b *ssa.Block) *ssa.Value {
	if b.Kind != block.BlockExit || len(b.Preds) != 1 || len(b.Values) != 1 || b.Controls[0].Op != ssaop.OpPanicBounds {
		return nil
	}
	return b.Controls[0]
}

func boundsPure(b *ssa.Block) bool {
	for _, v := range b.Values {
		switch v.Op {
		case ssaop.OpAdd32, ssaop.OpAdd64, ssaop.OpSub32, ssaop.OpSub64, ssaop.OpMul32, ssaop.OpMul64,
			ssaop.OpSlicemask, ssaop.OpAnd32, ssaop.OpAnd64, ssaop.OpAddPtr, ssaop.OpSliceMake, ssaop.OpStringMake,
			ssaop.OpSliceLen, ssaop.OpSliceCap, ssaop.OpSlicePtr, ssaop.OpStringLen, ssaop.OpStringPtr,
			ssaop.OpInlMark, ssaop.OpIsInBounds, ssaop.OpIsSliceInBounds, ssaop.OpConst32, ssaop.OpConst64, ssaop.OpCopy:
		default:
			return false
		}
	}
	return true
}
