module

public import M9StacksIntegration.CanonicalDivisorSpan
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeriesMorphism
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence

/-! The full actual divisor of one ORIGINAL pencil section.
Its length, line, and canonical restriction rank are derived. Base
points and nonreduced zeros are retained; no generation hypothesis or
moving-part replacement is imposed on the original pencil. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.LinearSeriesMorphism

universe u

namespace M9Native.PencilCanonicalDivisor

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (b : Module.Basis (Fin 2) K A.V)

def firstSection : Γ(A.L, ⊤) := seriesSections A b 0

theorem firstSection_ne_zero : firstSection f hdim A b ≠ 0 := seriesSections_ne_zero A b 0

def nativeSection : A.L.sections :=
  Stacks.PresheafOfModules.sectionOfTop A.L.val (firstSection f hdim A b)

theorem nativeSection_eval : (nativeSection f hdim A b).eval (op ⊤) = firstSection f hdim A b :=
  Stacks.PresheafOfModules.sectionOfTop_val_top A.L.val _

def divisor : X.IdealSheafData := by
  letI := A.isInvertible
  exact zeroScheme X A.L (firstSection f hdim A b)

theorem nativeSection_regular :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property (nativeSection f hdim A b) := by
  letI := A.isInvertible
  exact isRegularSection_of_eval_top_ne_zero A.L (nativeSection f hdim A b)
    ((nativeSection_eval f hdim A b).symm ▸ firstSection_ne_zero f hdim A b)

/-- Genuine effective Cartier structure on the original zero scheme. -/
theorem divisor_cartier : Stacks.Divisors.IsEffectiveCartierDivisor (divisor f hdim A b) := by
  letI := A.isInvertible
  have h := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X A.L
    (nativeSection f hdim A b)).mpr (nativeSection_regular f hdim A b)
  simpa only [nativeSection_eval, divisor] using h

/-- Honest finiteness of the full original scheme. -/
theorem divisor_finite : IsFinite ((divisor f hdim A b).subschemeι ≫ f) := by
  letI := A.isInvertible
  have h := isFinite_zeroScheme_of_eval_top_ne_zero K f hdim A.L (nativeSection f hdim A b)
    ((nativeSection_eval f hdim A b).symm ▸ firstSection_ne_zero f hdim A b)
  rw [nativeSection_eval f hdim A b] at h
  exact h

/-- The native divisor sheaf is the ORIGINAL pencil line. -/
def pencilLineIsoDivisor : A.L ≅ Stacks.Divisors.invertibleSheaf' (divisor f hdim A b) := by
  letI := A.isInvertible
  have e := invertibleSheafIsoZeroSchemeOfIsRegularSection A.L (nativeSection f hdim A b)
    (nativeSection_regular f hdim A b)
  simpa only [nativeSection_eval, divisor] using e

/-- Original-field structural H0 counts exactly the original degree d. -/
theorem divisor_length :
    letI : Algebra K Γ((divisor f hdim A b).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((divisor f hdim A b).subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank K Γ((divisor f hdim A b).subscheme, ⊤) = d := by
  letI := A.isInvertible
  letI : Algebra K Γ((divisor f hdim A b).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ ((divisor f hdim A b).subschemeι ≫ f).appTop).hom.toAlgebra
  have h := invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one K f hdim
    A.L (nativeSection f hdim A b) ((nativeSection_eval f hdim A b).symm ▸ firstSection_ne_zero f hdim A b)
    (divisor f hdim A b) (by rw [nativeSection_eval]; rfl)
  rw [A.degree_eq] at h
  omega

/-- Both original pencil classes are still present in H0(O(D)). -/
theorem divisor_h0_ge_two : 2 ≤ Module.finrank K
    (cohomologyOverField K f (Stacks.Divisors.invertibleSheaf' (divisor f hdim A b)) 0) := by
  letI := A.isInvertible
  letI := CurveDivisorSections.invertible_cohomology_zero_finite f A.L
  have hV : 2 ≤ Module.finrank K (cohomologyOverField K f A.L 0) := by
    have h := Submodule.finrank_le A.V
    rw [A.finrank_eq] at h
    exact h
  have h := (cohomologyOverFieldIso K f (pencilLineIsoDivisor f hdim A b) 0).toLinearEquiv.finrank_eq
  omega

/-- The actual canonical evaluation rank is bounded by d-1, for the
original pencil with all its base points and nonreduced zeros. -/
theorem canonical_restriction_rank_le :
    Module.finrank K (LinearMap.range
      (CanonicalDivisorSpan.canonicalRestriction f (divisor f hdim A b))) ≤ d-1 := by
  letI := divisor_cartier f hdim A b
  have h := CanonicalDivisorSpan.restriction_rank_le_length_sub_one f (divisor f hdim A b)
    (divisor_h0_ge_two f hdim A b)
  rw [divisor_length f hdim A b] at h
  exact h

end M9Native.PencilCanonicalDivisor
