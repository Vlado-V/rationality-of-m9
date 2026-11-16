module

public import M9StacksIntegration.GenusNineTricanonicalCohomology
public import M9StacksIntegration.Private.CurveClosedImmersionHilbert
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.VeryAmpleLargeDegree

/-! Every smooth proper genus-nine curve with constant global functions has
an actual complete tricanonical embedding in the native P³⁹. The degree-two
separation theorem applies to its original degree-forty-eight line, without
a restriction on pencils. The original hyperplane pullback is retained. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory
universe u
namespace M9Native.GenusNineTricanonicalEmbedding
open GenusNineTricanonicalCohomology
variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

theorem tricanonical_surjectsOnDegreeTwo (hg : genus f = 9) :
    SurjectsOnDegreeTwo f (tricanonical f) := by
  let S : CohenMacaulayCurveSituation :=
    { k := k, X := X, f := f,
      dimension_one := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f) }
  apply S.surjectsOnDegreeTwo_of_two_mul_genus_add_one_le (tricanonical f)
  change 2 * (genus f : ℤ) + 1 ≤
    invertibleCurveDegree k f (le_of_eq S.dimension_one) (tricanonical f)
  rw [tricanonical_degree f _ hg, hg]
  norm_num

theorem exists_tricanonical_closedImmersion [IsAlgClosed k] (hg : genus f = 9) :
    ∃ φ : X ⟶ projectiveSpaceOver 39 (Spec (.of k)),
      IsClosedImmersion φ ∧
      φ ≫ Stacks.Tag01VT.projectiveSpaceHom 39 (Spec (.of k)) = f ∧
      Nonempty ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 39 (Spec (.of k))) ≅
          tricanonical f) := by
  exact CompleteProjectiveLinearSystem.exists_closedImmersion_of_h0_eq_and_degree_two_separation
    f (tricanonical f) 39 (tricanonical_h0 f
      (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le hg)
    (tricanonical_surjectsOnDegreeTwo f hg)

theorem tricanonical_hilbertPolynomial
    (φ : X ⟶ projectiveSpaceOver 39 (Spec (.of k))) [IsClosedImmersion φ]
    (hover : φ ≫ Stacks.Tag01VT.projectiveSpaceHom 39 (Spec (.of k)) = f)
    (e : (Scheme.Modules.pullback φ).obj
      (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf 39 (Spec (.of k))) ≅
        tricanonical f) (hg : genus f = 9) (m : ℤ) :
    letI := CurveClosedImmersionHilbert.pushforward_unit_isCoherent φ
    hilbertPolynomial k 39 ((Scheme.Modules.pushforward φ).obj
      (SheafOfModules.unit X.ringCatSheaf)) m = 48 * m - 8 := by
  have h := CurveClosedImmersionHilbert.hilbertPolynomial_eq_of_pullback_iso φ f
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le hover (tricanonical f) e m
  rw [tricanonical_degree f _ hg, hg] at h
  exact h.trans (by ring)

end M9Native.GenusNineTricanonicalEmbedding
end
