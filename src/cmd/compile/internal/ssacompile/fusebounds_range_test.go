// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"testing"

	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/block"
	"cmd/compile/internal/ssa/ssaop"
	"cmd/compile/internal/types"
)

// No slice operations: only dominating scalar range facts distinguish these
// graphs. The first guard's success must not supply its own overflow proof.
func TestFuseBoundsDominatingRange(t *testing.T) {
	for _, mode := range []string{"bounded", "upper-only", "nonnegative-only"} {
		t.Run(mode, func(t *testing.T) {
			c := testConfig(t)
			typ := c.config.Types.Int64
			relation, lhs, rhs := ssaop.OpLeq64U, "i", "maximum"
			if mode == "upper-only" {
				relation = ssaop.OpLeq64
			}
			if mode == "nonnegative-only" {
				relation, lhs, rhs = ssaop.OpLeq64, "zero", "i"
			}
			fun := c.Fun("entry",
				Bloc("entry",
					Valu("mem", ssaop.OpInitMem, types.TypeMem, 0, nil),
					Valu("i", ssaop.OpArg, typ, 0, nil),
					Valu("n", ssaop.OpConst64, typ, 16, nil),
					Valu("maximum", ssaop.OpConst64, typ, 1024, nil),
					Valu("zero", ssaop.OpConst64, typ, 0, nil),
					Valu("k", ssaop.OpConst64, typ, 3, nil),
					Valu("range", relation, c.config.Types.Bool, 0, nil, lhs, rhs),
					If("range", "first", "out")),
				Bloc("first",
					Valu("first", ssaop.OpIsSliceInBounds, c.config.Types.Bool, 0, nil, "i", "n"),
					If("first", "window", "p1")),
				Bloc("window",
					Valu("remaining", ssaop.OpSub64, typ, 0, nil, "n", "i"),
					Valu("second", ssaop.OpIsInBounds, c.config.Types.Bool, 0, nil, "k", "remaining"),
					If("second", "done", "p2")),
				Bloc("p1", Valu("panic1", ssaop.OpPanicBounds, types.TypeMem, int64(ssa.BoundsSliceB), nil, "i", "n", "mem"), Exit("panic1")),
				Bloc("p2", Valu("panic2", ssaop.OpPanicBounds, types.TypeMem, int64(ssa.BoundsIndex), nil, "k", "remaining", "mem"), Exit("panic2")),
				Bloc("done", Exit("mem")),
				Bloc("out", Exit("mem")))
			checkFunc(fun.f)
			prove(fun.f)
			checkFunc(fun.f)
			fused := fun.blocks["window"].Kind == block.BlockPlain
			if fused != (mode != "upper-only") {
				t.Fatalf("fused=%v; want %v", fused, mode != "upper-only")
			}
		})
	}
}

// Signed end overflow is safe because bounds checks compare unsigned values.
// Exercise lengths near MaxInt without allocating impossibly large slices.
func TestFusedBoundsSignedOverflow(t *testing.T) {
	for _, maximum := range []uint64{1<<31 - 1, 1<<63 - 1} {
		values := []uint64{0, 1, 3, maximum - 3, maximum - 1, maximum}
		for _, firstStrict := range []bool{false, true} {
			for _, secondStrict := range []bool{false, true} {
				for _, n := range values {
					for _, i := range values {
						for _, k := range values {
							if firstStrict && !secondStrict && k == 0 {
								continue
							}
							first, remaining, end := i <= n, k <= n-i, i+k <= n
							if maximum == 1<<31-1 {
								remaining = uint32(k) <= uint32(n-i)
							}
							if firstStrict {
								first = i < n
							}
							if secondStrict {
								remaining, end = k < n-i, i+k < n
								if maximum == 1<<31-1 {
									remaining = uint32(k) < uint32(n-i)
								}
							}
							if (first && remaining) != end {
								t.Fatalf("max=%d i=%d k=%d n=%d strict=%v/%v", maximum, i, k, n, firstStrict, secondStrict)
							}
						}
					}
				}
			}
		}
	}
}
