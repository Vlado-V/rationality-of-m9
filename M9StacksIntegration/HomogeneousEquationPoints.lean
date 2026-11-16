module

public import M9StacksIntegration.HomogeneousEquationIdeal

/-! Actual scheme points of a finite homogeneous zero scheme contain
the original forms in their homogeneous prime. This is derived from the
genuine graded quotient's ideal sheaf; no pointwise ideal definition. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart

universe u v
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.HomogeneousEquationPoints

variable (K : Type u) [CommRing K] (n d : ℕ)
    {ι : Type v} [Finite ι] (F : ι → polyGrading K n d)

def ideal : (AlgebraicGeometry.Proj (polyGrading K n)).IdealSheafData :=
  ⨆ i, HomogeneousEquationIdeal.equationIdeal K n d F i

theorem form_mem_homogeneousPrime (x : (ideal K n d F).subscheme) (i : ι) :
    (F i : MvPolynomial (Fin (n+1)) K) ∈
      ((ideal K n d F).subschemeι x).asHomogeneousIdeal := by
  let p := (ideal K n d F).subschemeι x
  have hs : p ∈ (ideal K n d F).supportSet := by
    have hr := congrArg (fun S : Set (AlgebraicGeometry.Proj (polyGrading K n)) => p ∈ S)
      (Scheme.IdealSheafData.range_subschemeι (ideal K n d F))
    exact hr.mp ⟨x, rfl⟩
  have hs' : p ∈ (homogeneousIdealSheaf (polyGrading K n)
      (HomogeneousEquationIdeal.homogeneousSpan K n d F)).supportSet := by
    rw [HomogeneousEquationIdeal.homogeneousIdealSheaf_eq_iSup_equationIdeal]
    exact hs
  have hI := (mem_supportSet_homogeneousIdealSheaf_iff (polyGrading K n)
    (HomogeneousEquationIdeal.homogeneousSpan K n d F) p).mp hs'
  exact hI (Ideal.subset_span ⟨i, rfl⟩)

end M9Native.HomogeneousEquationPoints
