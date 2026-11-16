module

public import M9StacksIntegration.MukaiCanonicalExteriorCohomologyCore
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DegreeExteriorDeterminant
public import StacksFrontier.AlgebraicGeometry.InvertibleModuleEndomorphismOverField

/-!
# The actual degree of a canonical rank-three bundle

The given top-exterior identification proves the native canonical sheaf
invertible. Native Serre duality and the actual one-dimensional endomorphism
space give h¹(ω)=1; native h⁰(ω)=g and line Riemann--Roch give deg(ω)=2g−2.
The genuine native determinant-degree theorem then gives deg(E)=2g−2.
No canonical-degree or cohomological dimension equality is a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace M9Native.MukaiCanonicalExteriorCohomology

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

include hdim d

/-- Native Serre duality and the actual scalar endomorphisms of the
canonical line prove h¹(ω)=1. -/
theorem canonical_h1_eq_one_of_topExteriorIso :
    Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) =
      1 := by
  let := modulesLinearOverField k f
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    canonical_isInvertible_of_topExteriorIso f E d
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  let : (Stacks.Duality.dualizingSheafOverField f).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k f
      (Stacks.Duality.dualizingSheafOverField f) 1
  let : Module.Finite k
      (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) :=
    finiteDimensional_cohomologyOverField_of_isProper k f _ 1
  have h : Module.finrank k ((Stacks.Duality.dualizingSheafOverField f) ⟶
      (Stacks.Duality.dualizingSheafOverField f)) =
      Module.finrank k (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 1) :=
    (Stacks.Duality.homDualizingSheafLinearEquiv f hdim
      (Stacks.Duality.dualizingSheafOverField f)
      (isQuasicoherent_of_isCoherent _)).finrank_eq.trans Subspace.dual_finrank_eq
  exact h.symm.trans (finrank_end_eq_one_of_isInvertible k f _)

/-- The actual native canonical degree is calculated from its actual
H⁰ and H¹ using the actual line-bundle Riemann--Roch theorem. -/
theorem canonical_invertibleCurveDegree_of_topExteriorIso :
    letI := canonical_isInvertible_of_topExteriorIso f E d
    invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) =
      2 * (genus f : ℤ) - 2 := by
  let := canonical_isInvertible_of_topExteriorIso f E d
  have h := finrank_sub_finrank_eq_invertibleCurveDegree_add_genus k f hdim
    (Stacks.Duality.dualizingSheafOverField f)
  rw [Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f hdim,
    canonical_h1_eq_one_of_topExteriorIso k f hdim E d] at h
  push_cast at h
  linarith

/-- The canonical determinant forces deg(E)=2g−2 by the native degree
of the actual top exterior power and the canonical degree just calculated. -/
theorem canonical_curveDegree :
    curveDegree k f hdim E 3 = 2 * (genus f : ℤ) - 2 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (exteriorCube E) 1 :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  let := canonical_isInvertible_of_topExteriorIso f E d
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Stacks.Duality.dualizingSheafOverField f) 1 :=
    SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X _
  calc
    curveDegree k f hdim E 3 = curveDegree k f hdim (exteriorCube E) 1 :=
      curveDegree_eq_curveDegree_exteriorPower_of_isProper k f hdim 3 E
    _ = curveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) 1 :=
      curveDegree_eq_of_iso k f hdim 1 d
    _ = invertibleCurveDegree k f hdim (Stacks.Duality.dualizingSheafOverField f) :=
      (invertibleCurveDegree_eq_curveDegree k f hdim _).symm
    _ = 2 * (genus f : ℤ) - 2 :=
      canonical_invertibleCurveDegree_of_topExteriorIso k f hdim E d

theorem canonical_curveDegree_genus_nine (hg : genus f = 9) :
    curveDegree k f hdim E 3 = 16 := by
  have h := canonical_curveDegree k f hdim E d
  rw [hg] at h
  norm_num at h
  exact h

end M9Native.MukaiCanonicalExteriorCohomology
