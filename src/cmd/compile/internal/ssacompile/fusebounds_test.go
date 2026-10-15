// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package ssacompile

import (
	"fmt"
	"testing"

	"cmd/compile/internal/ssa"
	"cmd/compile/internal/ssa/block"
	"cmd/compile/internal/ssa/ssaop"
	"cmd/compile/internal/types"
)

// These graphs contain no SliceMake, SliceLen, SliceCap or slice pointers.
func TestFuseScalarBounds(t *testing.T) {
	for _, word := range []int{32, 64} {
		for _, shifted := range []bool{false, true} {
			for _, inclusive := range []bool{false, true} {
				t.Run(fmt.Sprintf("%d/shifted=%v/inclusive=%v", word, shifted, inclusive), func(t *testing.T) {
					c := testConfig(t)
					integer := c.config.Types.Int64
					constant, add, sub, ext := ssaop.OpConst64, ssaop.OpAdd64, ssaop.OpSub64, ssaop.OpZeroExt8to64
					if word == 32 {
						integer = c.config.Types.Int32
						constant, add, sub, ext = ssaop.OpConst32, ssaop.OpAdd32, ssaop.OpSub32, ssaop.OpZeroExt8to32
					}
					kind := ssaop.OpIsInBounds
					if inclusive {
						kind = ssaop.OpIsSliceInBounds
					}
					index, limit := "k", "remaining"
					if shifted {
						index, limit = "j", "n"
					}
					fun := c.Fun("entry",
						Bloc("entry",
							Valu("mem", ssaop.OpInitMem, types.TypeMem, 0, nil),
							Valu("arg", ssaop.OpArg, c.config.Types.UInt8, 0, nil),
							Valu("i", ext, integer, 0, nil, "arg"),
							Valu("n", constant, integer, 16, nil),
							Valu("k", constant, integer, 3, nil),
							Valu("first", kind, c.config.Types.Bool, 0, nil, "i", "n"),
							If("first", "window", "p1")),
						Bloc("window",
							Valu("remaining", sub, integer, 0, nil, "n", "i"),
							Valu("j", add, integer, 0, nil, "i", "k"),
							Valu("second", kind, c.config.Types.Bool, 0, nil, index, limit),
							If("second", "done", "p2")),
						Bloc("p1", Valu("panic1", ssaop.OpPanicBounds, types.TypeMem, int64(ssa.BoundsSliceB), nil, "i", "n", "mem"), Exit("panic1")),
						Bloc("p2", Valu("panic2", ssaop.OpPanicBounds, types.TypeMem, int64(ssa.BoundsIndex), nil, index, limit, "mem"), Exit("panic2")),
						Bloc("done", Exit("mem")))
					checkFunc(fun.f)
					prove(fun.f)
					checkFunc(fun.f)
					if fun.blocks["window"].Kind != block.BlockPlain || len(fun.f.Blocks) != 6 {
						t.Fatal("did not fuse scalar bounds guards")
					}
					if fun.blocks["entry"].Controls[0].Op != kind {
						t.Fatal("changed strictness of combined bounds guard")
					}
					if fun.values["panic1"].AuxInt != int64(ssa.BoundsSliceB) || fun.values["panic2"].AuxInt != int64(ssa.BoundsIndex) {
						t.Fatal("changed panic kind")
					}
				})
			}
		}
	}
}

// Exhaust the truth-table underlying both generic guard transformations.
func TestFusedBoundsGuardEquivalence(t *testing.T) {
	for _, firstStrict := range []bool{false, true} {
		for _, secondStrict := range []bool{false, true} {
			for n := int64(0); n < 20; n++ {
				for i := int64(0); i < 25; i++ {
					for k := int64(0); k < 8; k++ {
						if firstStrict && !secondStrict && k == 0 {
							continue
						}
						first := i <= n
						if firstStrict {
							first = i < n
						}
						remaining := k <= n-i
						shifted := i+k <= n
						if secondStrict {
							remaining = k < n-i
							shifted = i+k < n
						}
						if (first && remaining) != shifted {
							t.Fatalf("i=%d k=%d n=%d strict=%v/%v", i, k, n, firstStrict, secondStrict)
						}
					}
				}
			}
		}
	}
}
