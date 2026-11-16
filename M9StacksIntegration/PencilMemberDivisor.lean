module

public import M9StacksIntegration.PencilCanonicalDivisor
public import M9StacksIntegration.CanonicalDivisorEvaluation

/-!
# The actual full divisor of any nonzero original pencil member

The member is an actual nonzero class of the original two-dimensional
pencil space. Its full zero scheme, including base points and
nilpotents, is Cartier of the original degree. Its divisor line is the
original pencil line, so genuine Riemann--Roch bounds canonical rank.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.PencilMemberDivisor

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) {d : ℕ}
    (A : LinearSeries K f hdim d 1) (x : A.V)

/-- The actual class in the original-field linear H0/section comparison. -/
def memberSection : Γ(A.L, ⊤) :=
  (cohomologyOverFieldZeroLinearIso K f A.L).hom (x : cohomologyOverField K f A.L 0)

theorem section_ne_zero (hx : x ≠ 0) : memberSection f hdim A x ≠ 0 := by
  intro hs
  apply hx
  apply Subtype.ext
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso K f A.L).hom).1
  change memberSection f hdim A x =
    (cohomologyOverFieldZeroLinearIso K f A.L).hom 0
  exact hs.trans ((cohomologyOverFieldZeroLinearIso K f A.L).hom.hom.map_zero).symm

def nativeSection : A.L.sections :=
  Stacks.PresheafOfModules.sectionOfTop A.L.val (memberSection f hdim A x)

theorem nativeSection_eval :
    (nativeSection f hdim A x).eval (op ⊤) = memberSection f hdim A x :=
  Stacks.PresheafOfModules.sectionOfTop_val_top A.L.val _

def divisor : X.IdealSheafData := by
  let := A.isInvertible
  exact zeroScheme X A.L (memberSection f hdim A x)

variable [IsCurve K f]

theorem nativeSection_regular (hx : x ≠ 0) :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property (nativeSection f hdim A x) := by
  let := A.isInvertible
  exact isRegularSection_of_eval_top_ne_zero A.L (nativeSection f hdim A x)
    ((nativeSection_eval f hdim A x).symm ▸ section_ne_zero f hdim A x hx)

theorem divisor_cartier (hx : x ≠ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor (divisor f hdim A x) := by
  let := A.isInvertible
  have h := (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X A.L
    (nativeSection f hdim A x)).mpr (nativeSection_regular f hdim A x hx)
  simpa only [nativeSection_eval, divisor] using h

theorem divisor_finite (hx : x ≠ 0) :
    IsFinite ((divisor f hdim A x).subschemeι ≫ f) := by
  let := A.isInvertible
  have h := isFinite_zeroScheme_of_eval_top_ne_zero K f hdim A.L
    (nativeSection f hdim A x)
    ((nativeSection_eval f hdim A x).symm ▸ section_ne_zero f hdim A x hx)
  rw [nativeSection_eval f hdim A x] at h
  exact h

/-- The original line is retained for the entire original zero scheme. -/
def pencilLineIsoDivisor (hx : x ≠ 0) :
    A.L ≅ Stacks.Divisors.invertibleSheaf' (divisor f hdim A x) := by
  let := A.isInvertible
  have e := invertibleSheafIsoZeroSchemeOfIsRegularSection A.L (nativeSection f hdim A x)
    (nativeSection_regular f hdim A x hx)
  simpa only [nativeSection_eval, divisor] using e

theorem divisor_length (hx : x ≠ 0) :
    let : Algebra K Γ((divisor f hdim A x).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((divisor f hdim A x).subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank K Γ((divisor f hdim A x).subscheme, ⊤) = d := by
  let := A.isInvertible
  let : Algebra K Γ((divisor f hdim A x).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ ((divisor f hdim A x).subschemeι ≫ f).appTop).hom.toAlgebra
  have h := invertibleCurveDegree_eq_finrank_globalSections_zeroScheme_of_dim_le_one K f hdim
    A.L (nativeSection f hdim A x)
    ((nativeSection_eval f hdim A x).symm ▸ section_ne_zero f hdim A x hx)
    (divisor f hdim A x) (by rw [nativeSection_eval]; rfl)
  rw [A.degree_eq] at h
  omega

theorem divisor_h0_ge_two (hx : x ≠ 0) :
    2 ≤ Module.finrank K (cohomologyOverField K f
      (Stacks.Divisors.invertibleSheaf' (divisor f hdim A x)) 0) := by
  let := A.isInvertible
  let := CurveDivisorSections.invertible_cohomology_zero_finite f A.L
  have hV : 2 ≤ Module.finrank K (cohomologyOverField K f A.L 0) := by
    have h := Submodule.finrank_le A.V
    rw [A.finrank_eq] at h
    exact h
  have h := (cohomologyOverFieldIso K f (pencilLineIsoDivisor f hdim A x hx) 0).toLinearEquiv.finrank_eq
  omega

variable [Smooth f] [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

/-- The full native canonical restriction rank is bounded by d-1. -/
theorem canonical_restriction_rank_le (hx : x ≠ 0) :
    Module.finrank K (LinearMap.range
      (CanonicalDivisorSpan.canonicalRestriction f (divisor f hdim A x))) ≤ d-1 := by
  let := divisor_cartier f hdim A x hx
  have h := CanonicalDivisorSpan.restriction_rank_le_length_sub_one f (divisor f hdim A x)
    (divisor_h0_ge_two f hdim A x hx)
  rw [divisor_length f hdim A x hx] at h
  exact h

/-- Every actual coordinate system restricts through this genuine full
zero divisor with the same derived rank bound. -/
theorem canonical_evaluation_rank_le {V : Type u} [AddCommGroup V] [Module K V]
    [Module.Finite K V] (hx : x ≠ 0)
    (c : V →ₗ[K] cohomologyOverField K f (Stacks.Duality.dualizingSheafOverField f) 0) :
    Module.finrank K (LinearMap.range
      ((CanonicalDivisorEvaluation.evaluation f (divisor f hdim A x)
        (Stacks.Duality.dualizingSheafOverField f)).comp c)) ≤ d-1 := by
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Duality.dualizingSheafOverField f) :=
    CurveCanonicalInvertibility.dualizing_isInvertible f
  let := CurveDivisorSections.invertible_cohomology_zero_finite f
    (Stacks.Duality.dualizingSheafOverField f)
  exact (CanonicalDivisorEvaluation.evaluation_comp_rank_le f _ _ c).trans
    (canonical_restriction_rank_le f hdim A x hx)

end M9Native.PencilMemberDivisor
