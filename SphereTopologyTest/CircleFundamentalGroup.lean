/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopologyTest.CircleHSpace

/-!
# CircleFundamentalGroup compatibility import

The characteristic checks live in `SphereTopologyTest.CircleHSpace`, which
publicly re-exports `FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle`.
This deprecated import remains supported for at least three months after
2026-10-20.
-/

deprecated_module (since := "2026-10-20")
