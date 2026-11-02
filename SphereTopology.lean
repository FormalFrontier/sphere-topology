/-
SPDX-License-Identifier: Apache-2.0
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formal Frontier Agents
-/
-- Contributors: Formal Frontier Agents, including Prism.
-- See docs/CREDITS.md for mathematical and interface credit.
module

public import SphereTopology.Geometry.CubeSphere
public import SphereTopology.Geometry.ForwardRay
public import SphereTopology.Geometry.ForwardRayMap
public import SphereTopology.Geometry.OnePointSphere
public import SphereTopology.Geometry.Projectivization
public import SphereTopology.Geometry.Stereographic
public import SphereTopology.Geometry.SpherePinch
public import SphereTopology.Geometry.SphereCoordinateReflection
public import SphereTopology.Homotopy.HomotopyGroup.Sphere
public import SphereTopology.Homotopy.HomotopyGroup.SphereHom
public import SphereTopology.Homotopy.HomotopyGroup.SphereNontrivial
public import SphereTopology.Homotopy.HomotopyGroup.SphereCogroup
public import SphereTopology.Homotopy.HomotopyGroup.SpherePinch
public import SphereTopology.Homotopy.HomotopyGroup.SpherePinchFold
public import SphereTopology.Homotopy.HomotopyGroup.SphereCoordinateReflection
public import SphereTopology.Homotopy.SphereCogroup
public import SphereTopology.Homotopy.SphereCocommutativity
public import SphereTopology.Homotopy.HSpaceFundamentalGroup
public import SphereTopology.Homotopy.Projectivization
public import SphereTopology.Homotopy.Sphere
public import SphereTopology.Homotopy.TangentField
public import FundamentalGroupoids.Topology.Covering.Lifting
public import SphereTopology.Topology.SingularLifts
public import FundamentalGroupoids.Topology.Category.TopCat.Limits.WidePushout
public import SphereTopology.Topology.WidePushoutRetraction
public import SphereTopology.Topology.WidePushout.ClosedMap
public import SphereTopology.Topology.WidePushout.Separation
public import SphereTopology.Topology.WidePushout.Compactness
public import SphereTopology.Topology.WidePushout.OpenNeighborhood
public import SphereTopology.Topology.WidePushout.PointLift
public import SphereTopology.Topology.WidePushout.Chart
public import SphereTopology.Topology.WidePushout.FundamentalGroup
public import SphereTopology.Topology.WidePushout.FundamentalGroupKernel
public import SphereTopology.Topology.WidePushout.SubsetRetraction
public import SphereTopology.Topology.WidePushout.Subfamily
public import SphereTopology.Topology.WidePushout.SubfamilyHomotopy
public import FundamentalGroupoids.Topology.Homotopy.WidePushout
public import SphereTopology.Topology.WidePushout.PointHomotopyEquiv
public import FundamentalGroupoids.Topology.Covering.DeckGroup
public import FundamentalGroupoids.Topology.Covering.DeckMonodromy
public import FundamentalGroupoids.Topology.Covering.Monodromy
public import FundamentalGroupoids.Topology.Covering.Equivalence
public import SphereTopology.Homology.Singular.Transfer
public import FundamentalGroupoids.AlgebraicTopology.FundamentalGroup.Circle
public import SphereTopology.Homotopy.CircleBouquet
public import SphereTopology.Homotopy.CircleBouquet.ClosedMap
public import SphereTopology.Homotopy.CircleBouquet.FundamentalGroup
public import SphereTopology.Homotopy.CircleBouquet.Presentation
public import SphereTopology.Homotopy.CircleBouquet.Topology
public import SphereTopology.Homotopy.CircleDegree
public import SphereTopology.Homotopy.Disk
public import SphereTopology.Homology.Singular.SmallChains
public import SphereTopology.Homology.Singular.MayerVietoris
public import SphereTopology.Homology.Singular.Components
public import SphereTopology.Homology.Singular.Reduced
public import SphereTopology.Homology.Singular.Connectedness
public import SphereTopology.Homology.Singular.ReducedMayerVietoris
public import SphereTopology.Homology.Singular.Circle
public import SphereTopology.Homology.Singular.Sphere
public import SphereTopology.Homology.Singular.SphereAntipodal
public import SphereTopology.Homotopy.HairyBallSphere2

/-!
# Sphere topology and integral singular homology

Public aggregate for the production library. Regression clients and diagnostics
are compiled separately by the default test target.
-/
