/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SphereTopology.Homology.Singular.SphereAntipodal
public import SphereTopology.Homotopy.HomotopyGroup.SphereHom
public import SphereTopology.Homotopy.SphereCogroup

/-!
# Nontrivial homotopy classes of the metric two-sphere

The identity of the universe-lifted metric two-sphere is not homotopic to a
constant map. In the based-homotopy category its identity class differs from
the constant class at the last-axis north pole. The corresponding second
homotopy group is nontrivial.

The sphere is `Metric.Sphere.basedSpace 1`, whose underlying space is the
universe lift of the unit sphere in `EuclideanSpace ℝ (Fin 3)`. The homotopy
group and the based-homotopy quotient retain their existing definitions and
operations. No computation of the second homotopy group is asserted.

## References

* This library's `SphereTopology.sphere2_id_not_homotopic_antipodal` supplies
  the unbased obstruction on the unlifted sphere. Its inputs are the integral
  second homology calculation in `SphereTopology.Homology.Singular.Sphere`
  and the antipodal action in `SphereTopology.Homology.Singular.SphereAntipodal`.
  The antipodal map is not used as a north-based map.
* Mathlib supplies `contractible_iff_id_nullhomotopic`,
  `Homeomorph.contractibleSpace_iff`, `Homeomorph.ulift` and the passage from
  relative homotopy to ordinary homotopy.
* Fundamental Groupoids supplies the based-homotopy quotient and its
  equality criterion. This library's `HomotopyGroup.equivSphereHom` supplies
  the comparison with sphere-map classes.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory

namespace Metric.Sphere

/-- The identity of the universe-lifted metric two-sphere is not homotopic to
any constant map. -/
theorem id_not_nullhomotopic_two :
    ¬ ContinuousMap.Nullhomotopic (ContinuousMap.id (basedSpace.{u} 1).right) := by
  intro h
  rw [basedSpace_right] at h
  have hLift : ContractibleSpace (ULift.{u} SphereTopology.sphere2) :=
    (contractible_iff_id_nullhomotopic _).mpr h
  have hSmall : ContractibleSpace SphereTopology.sphere2 :=
    (Homeomorph.ulift.{u, 0} (X := SphereTopology.sphere2)).contractibleSpace_iff.mp hLift
  obtain ⟨p, hp⟩ := (contractible_iff_id_nullhomotopic _).mp hSmall
  apply SphereTopology.sphere2_id_not_homotopic_antipodal
  -- Precomposition fixes the constant value; no basedness of the antipodal map is used.
  have hAntipodal : ContinuousMap.Homotopic SphereTopology.sphere2Antipodal.hom
      (ContinuousMap.const SphereTopology.sphere2 p) := by
    simpa only [ContinuousMap.id_comp, ContinuousMap.const_comp] using
      hp.comp (ContinuousMap.Homotopic.refl SphereTopology.sphere2Antipodal.hom)
  exact hp.trans hAntipodal.symm

/-- In the north-based homotopy category, the identity of the metric two-sphere
and its north-constant endomorphism have distinct classes. -/
theorem homotopyQuotient_id_ne_const_two :
    (BasedTopCat.homotopyQuotient.{u}).map (𝟙 (basedSpace.{u} 1)) ≠
      (BasedTopCat.homotopyQuotient.{u}).map
        (BasedTopCat.ofHom
          (X := (basedSpace.{u} 1).right) (Y := (basedSpace.{u} 1).right)
          (x := BasedTopCat.point (basedSpace.{u} 1))
          (y := BasedTopCat.point (basedSpace.{u} 1))
          (ContinuousMap.const (basedSpace.{u} 1).right
            (BasedTopCat.point (basedSpace.{u} 1))) rfl) := by
  intro h
  apply id_not_nullhomotopic_two.{u}
  refine ⟨BasedTopCat.point (basedSpace.{u} 1), ?_⟩
  have hConst :
      (BasedTopCat.ofHom
        (X := (basedSpace.{u} 1).right) (Y := (basedSpace.{u} 1).right)
        (x := BasedTopCat.point (basedSpace.{u} 1))
        (y := BasedTopCat.point (basedSpace.{u} 1))
        (ContinuousMap.const (basedSpace.{u} 1).right
          (BasedTopCat.point (basedSpace.{u} 1))) rfl :
        basedSpace.{u} 1 ⟶ basedSpace.{u} 1).right.hom =
          ContinuousMap.const (basedSpace.{u} 1).right
            (BasedTopCat.point (basedSpace.{u} 1)) :=
    BasedTopCat.ofHom_right_hom
      (X := (basedSpace.{u} 1).right) (Y := (basedSpace.{u} 1).right)
      (x := BasedTopCat.point (basedSpace.{u} 1))
      (y := BasedTopCat.point (basedSpace.{u} 1))
      (ContinuousMap.const (basedSpace.{u} 1).right
        (BasedTopCat.point (basedSpace.{u} 1))) rfl
  have hHomotopy := ((BasedTopCat.homotopyQuotient_map_eq_iff _ _).mp h).homotopic
  erw [Under.id_right, TopCat.hom_id, hConst] at hHomotopy
  exact hHomotopy

end Metric.Sphere

namespace HomotopyGroup

/-- The second homotopy group of the universe-lifted metric two-sphere,
based at its last-axis north pole, is nontrivial. -/
theorem nontrivial_sphere_two :
    Nontrivial (HomotopyGroup (Fin 2) (Metric.Sphere.basedSpace.{u} 1).right
      (BasedTopCat.point (Metric.Sphere.basedSpace.{u} 1))) := by
  let X := Metric.Sphere.basedSpace.{u} 1
  let h : Nontrivial (BasedTopCat.homotopyQuotient.obj X ⟶
      BasedTopCat.homotopyQuotient.obj X) :=
    ⟨⟨_, _, Metric.Sphere.homotopyQuotient_id_ne_const_two.{u}⟩⟩
  apply (equivSphereHom 2 X).nontrivial_congr.mpr
  rw [← Metric.Sphere.basedSpace_eq_of.{u} 1]
  exact h

end HomotopyGroup
