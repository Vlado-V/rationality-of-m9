module

public import M9StacksIntegration.LagrangianPrimitiveRestriction
public import M9StacksIntegration.LagrangianUniversalSectionInjection
public import M9StacksIntegration.MukaiEvaluationChoices

/-!
# Original primitive restriction and the common-kernel obstruction

The actual exterior-pullback isomorphism compares the original restriction
line with the determinant of the literal pulled universal quotient. Its
H0 map preserves the original structural field action and every original
primitive section. Thus the independent geometric restriction-rank
producer can be consumed without a section-comparison premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianPrimitiveRestrictionInjection

open LagrangianPluckerQuotient LagrangianPullback LagrangianPrimitiveRestriction
open LagrangianKernelPrimitiveSections LagrangianQuotientExteriorEvaluation

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k]
  (f : X ⟶ Spec (.of k)) (l : X ⟶ LagrangianGrassmannian.space k)

/-- Actual native exterior pullback induces the original-k-linear H0 equivalence. -/
def determinantCohomologyEquiv :
    cohomologyOverField k f (restrictedLine k l) 0 ≃ₗ[k]
      cohomologyOverField k f
        (Scheme.Modules.exteriorPower (LagrangianUniversalSections.bundle k l) 3) 0 :=
  MukaiEvaluationChoices.cohomologyEquiv k f
    (exteriorPullbackIso l (quotientOnLG k).target 3) 0

/-- Every original restricted primitive section is retained by the true
determinant comparison, with the actual structural scalar action. -/
theorem determinantCohomologyEquiv_sectionH0
    (hl : l ≫ LagrangianGrassmannian.projection k = f) (i : Fin 14) :
    determinantCohomologyEquiv k f l (sectionH0 k f l i) =
      primitiveH0 k f (LagrangianUniversalSections.quotientMap k l) i := by
  apply (ConcreteCategory.bijective_of_isIso (cohomologyOverFieldZeroLinearIso k f
    (Scheme.Modules.exteriorPower (LagrangianUniversalSections.bundle k l) 3)).hom).injective
  refine (cohomologyOverFieldZeroLinearIso_cohomologyOverFieldMap k f
    (exteriorPullbackIso l (quotientOnLG k).target 3).hom (sectionH0 k f l i)).trans ?_
  rw [sectionH0, Iso.inv_hom_id_apply, primitiveH0, Iso.inv_hom_id_apply]
  have h := LagrangianPrimitiveSectionsPullback.primitiveSections_pullback k l i
  rw [LagrangianUniversalSections.coefficients k f l hl] at h
  exact h

/-- The genuine original restriction image and the genuine quotient
primitive-section span have exactly the same finite dimension. -/
theorem finrank_restriction_eq_primitive_span
    (hl : l ≫ LagrangianGrassmannian.projection k = f) :
    finrank k (LinearMap.range (primitiveRestriction k f l)) =
      finrank k (Submodule.span k (Set.range
        (primitiveH0 k f (LagrangianUniversalSections.quotientMap k l)))) := by
  let e := determinantCohomologyEquiv k f l
  have hf : e.toLinearMap ∘ sectionH0 k f l =
      primitiveH0 k f (LagrangianUniversalSections.quotientMap k l) := by
    funext i
    exact determinantCohomologyEquiv_sectionH0 k f l hl i
  have hm : (Submodule.span k (Set.range (sectionH0 k f l))).map e.toLinearMap =
      Submodule.span k (Set.range
        (primitiveH0 k f (LagrangianUniversalSections.quotientMap k l))) := by
    rw [Submodule.map_span, ← Set.range_comp, hf]
  rw [primitiveRestriction_range k f l, ← hm]
  exact (e.finrank_map_eq (Submodule.span k (Set.range (sectionH0 k f l)))).symm

variable [CharZero k]

theorem finrank_restriction_eq_range_lambda
    (hl : l ≫ LagrangianGrassmannian.projection k = f) :
    finrank k (LinearMap.range (primitiveRestriction k f l)) =
      finrank k (LinearMap.range
        (lambda k f (LagrangianUniversalSections.quotientMap k l) 3)) := by
  rw [finrank_restriction_eq_primitive_span k f l hl,
    ← range_primitiveEvaluation_eq_span,
    range_primitiveEvaluation k f _
      (LagrangianUniversalSectionInjection.universal_quotient_annihilates k l)]
  rfl

/-- The original universal six-section injection follows from the
independently produced actual primitive-restriction rank. No normalizer
or determinant-section comparison is supplied as an extra premise. -/
theorem universal_sectionMap_injective_of_restriction_rank
    (hl : l ≫ LagrangianGrassmannian.projection k = f)
    (hspan : 5 < finrank k (LinearMap.range (primitiveRestriction k f l))) :
    Function.Injective (LagrangianUniversalSections.sectionMap k f l) := by
  apply LagrangianUniversalSectionInjection.universal_sectionMap_injective_of_primitive_span k f l
  rw [← finrank_restriction_eq_primitive_span k f l hl]
  exact hspan

end M9Native.LagrangianPrimitiveRestrictionInjection
