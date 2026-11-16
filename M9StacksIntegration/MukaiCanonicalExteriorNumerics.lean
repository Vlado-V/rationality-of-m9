module

public import M9StacksIntegration.MukaiCanonicalExteriorDegree

/-!
# The intrinsic first-cohomology count of a canonical rank-three bundle

The actual canonical determinant gives degree `2g−2`; actual rank-three
Riemann--Roch then computes h¹(E)−h⁰(E)=g−1. In genus nine this is eight.
These are derived first-cohomology counts, not premises for wedge duality.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.MukaiCanonicalExteriorCohomology

variable {X : Scheme.{u}} (k : Type u) [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (d : exteriorCube E ≅ Stacks.Duality.dualizingSheafOverField f)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

include hdim d

/-- Actual determinant degree and actual Riemann--Roch compute the
first-cohomology count of E intrinsically. -/
theorem canonical_h1_sub_h0_identity :
    (Module.finrank k (cohomologyOverField k f E 1) : ℤ) -
      (Module.finrank k (cohomologyOverField k f E 0) : ℤ) = (genus f : ℤ) - 1 := by
  have hrr := rankThree_riemannRoch k f hdim E
  have hdeg := canonical_curveDegree k f hdim E d
  rw [hdeg] at hrr
  linarith

theorem canonical_h1_genus_nine (hg : genus f = 9) :
    Module.finrank k (cohomologyOverField k f E 1) =
      Module.finrank k (cohomologyOverField k f E 0) + 8 := by
  have h := canonical_h1_sub_h0_identity k f hdim E d
  rw [hg] at h
  norm_num at h
  omega

theorem canonical_h1_fourteen (hg : genus f = 9)
    (hE : Module.finrank k (cohomologyOverField k f E 0) = 6) :
    Module.finrank k (cohomologyOverField k f E 1) = 14 := by
  have h := canonical_h1_genus_nine k f hdim E d hg
  omega

end M9Native.MukaiCanonicalExteriorCohomology
