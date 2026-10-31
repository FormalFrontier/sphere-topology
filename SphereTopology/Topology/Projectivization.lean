/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.Topology.Constructions

/-!
# The quotient topology on projectivization

The projectivization of a module over a division ring carries the quotient topology
from its nonzero vectors. This is the quotient topology on Mathlib's
`Projectivization`, with no topology on the scalar ring and no continuity assumption
on scalar multiplication.

* `Projectivization.isQuotientMap_mk'` exposes the quotient universal property via
  `Topology.IsQuotientMap`, including its continuity and open-preimage criteria.
* `Projectivization.continuous_mk'` gives continuity of the quotient maker.

## References

* Mathlib's `LinearAlgebra.Projectivization.Basic` supplies the projectivization,
  its quotient maker, induction and scalar-equivalence APIs.
* Mathlib's `Topology.Constructions` supplies the quotient topology and its
  universal property.
-/

@[expose] public section

open Topology

universe u v

namespace Projectivization

variable (K : Type u) (V : Type v) [DivisionRing K] [AddCommGroup V] [Module K V]
  [TopologicalSpace V]

/-- The quotient topology on projectivization, inherited from the nonzero vectors. -/
instance instTopologicalSpace : TopologicalSpace (Projectivization K V) :=
  instTopologicalSpaceQuotient (s := projectivizationSetoid K V)

variable {V}

/-- The maker from nonzero vectors to projectivization is a quotient map. -/
theorem isQuotientMap_mk' : IsQuotientMap (mk' K (V := V)) :=
  isQuotientMap_quotient_mk' (s := projectivizationSetoid K V)

/-- The maker from nonzero vectors to projectivization is continuous. -/
@[continuity, fun_prop]
theorem continuous_mk' : Continuous (mk' K (V := V)) :=
  continuous_quotient_mk' (s := projectivizationSetoid K V)

end Projectivization
