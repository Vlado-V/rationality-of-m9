module

public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection
public import M9StacksIntegration.SectionZeroEvaluation

/-!
# The actual native zero scheme of the original first quotient section

The ideal is the native dual-evaluation zero ideal of the actual original
universal quotient section. Its full all-test-scheme factorization law is
derived, and the pulled original quotient has a literal first-section
relation. The resulting primitive restriction rank bound is a theorem
about the actual scheme, without a quadric or dimension premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

universe u

namespace M9Native.LagrangianCommonKernelZero

open LagrangianGrassmannian LagrangianMatrixChart LagrangianPluckerQuotient
open LagrangianIsotropicRestriction LagrangianQuotientExteriorEvaluation
open LagrangianKernelPrimitiveSections LagrangianPrimitiveRestriction

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable (k : Type u) [Field k]

local instance : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (quotientOnLG k).target :=
  (quotientOnLG k).finiteLocallyFree.isFiniteLocallyFree

/-- The literal first section of the original universal rank-three quotient. -/
def standardSection : Γ((quotientOnLG k).target, ⊤) :=
  Scheme.Modules.Hom.app (quotientOnLG k).map ⊤
    (freeBasisSection (LagrangianGrassmannian.space k) 6 0)

/-- The actual native section-zero ideal, retaining scheme structure. -/
abbrev zeroIdeal : (LagrangianGrassmannian.space k).IdealSheafData :=
  Stacks.Chow.zeroSchemeOfSection (LagrangianGrassmannian.space k)
    (quotientOnLG k).target (standardSection k)

abbrev zeroSpace : Scheme.{u} := (zeroIdeal k).subscheme

abbrev zeroInclusion : zeroSpace k ⟶ LagrangianGrassmannian.space k :=
  (zeroIdeal k).subschemeι

abbrev zeroProjection : zeroSpace k ⟶ Spec (.of k) :=
  zeroInclusion k ≫ LagrangianGrassmannian.projection k

instance zeroInclusion_isClosedImmersion : IsClosedImmersion (zeroInclusion k) := inferInstance

/-- The native ideal agrees with the literal evaluation ideal whose
finite-locally-free universal property was proved independently. -/
theorem zeroIdeal_eq_evaluationIdeal :
    zeroIdeal k = SectionZeroIdealFactorization.sectionZeroIdeal (LagrangianGrassmannian.space k)
      (quotientOnLG k).target (standardSection k) := by
  ext U
  rw [Stacks.Chow.SectionZeroScheme.zeroSchemeOfSection_ideal,
    SectionZeroIdealFactorization.sectionZeroIdeal_ideal]

/-- Vanishing on the actual native zero scheme, proved for the original section. -/
theorem pullback_standardSection_zero :
    pullbackGlobalSections (zeroInclusion k) (quotientOnLG k).target (standardSection k) = 0 := by
  have h := congrArg (fun I : (LagrangianGrassmannian.space k).IdealSheafData =>
    pullbackGlobalSections I.subschemeι (quotientOnLG k).target (standardSection k) = 0)
    (zeroIdeal_eq_evaluationIdeal k)
  exact h.mpr (SectionZeroIdealFactorization.pullbackGlobalSections_subschemeι_eq_zero
    (quotientOnLG k).target 3 (standardSection k))

/-- The genuine full factorization law on arbitrary native test schemes. -/
theorem factorsThrough_iff {T : Scheme.{u}} (l : T ⟶ LagrangianGrassmannian.space k) :
    pullbackGlobalSections l (quotientOnLG k).target (standardSection k) = 0 ↔
      ∃ t : T ⟶ zeroSpace k, t ≫ zeroInclusion k = l := by
  have h := congrArg (fun I : (LagrangianGrassmannian.space k).IdealSheafData =>
    ∃ t : T ⟶ I.subscheme, t ≫ I.subschemeι = l) (zeroIdeal_eq_evaluationIdeal k)
  exact (SectionZeroIdealFactorization.pullbackGlobalSections_eq_zero_iff_factorsThrough
    (quotientOnLG k).target 3 (standardSection k) l).trans (Iff.of_eq h.symm)

/-- The literal original quotient on the actual zero scheme kills its first basis section. -/
theorem quotient_first_section_zero :
    (LagrangianUniversalSections.quotientMap k (zeroInclusion k)).app ⊤
      (freeBasisSection (zeroSpace k) 6 0) = 0 := by
  change (pulledQuotient (zeroInclusion k) (quotientOnLG k).map).app ⊤
    (freeVector (zeroSpace k) 0) = 0
  rw [pulledQuotient_basis]
  exact pullback_standardSection_zero k

theorem original_first_section_relation :
    LagrangianUniversalSections.sectionMap k (zeroProjection k) (zeroInclusion k)
      (LagrangianField.basisVector k 0) = 0 := by
  rw [← LagrangianUniversalSectionInjection.originalSectionMap_eq_universal]
  rw [originalSectionMap_basis]
  apply (ConcreteCategory.bijective_of_isIso
    (cohomologyOverFieldZeroLinearIso k (zeroProjection k)
      (LagrangianUniversalSections.bundle k (zeroInclusion k))).hom).injective
  rw [originalSection_sections, map_zero]
  exact quotient_first_section_zero k

/-- The actual primitive-section image bound holds on the native zero scheme itself. -/
theorem primitive_span_le_five :
    finrank k (Submodule.span k (Set.range (primitiveH0 k (zeroProjection k)
      (LagrangianUniversalSections.quotientMap k (zeroInclusion k))))) ≤ 5 :=
  finrank_span_primitiveH0_le_five k (zeroProjection k) _ (quotient_first_section_zero k)

/-- The original restriction map on the actual native zero scheme has rank at most five. -/
theorem primitiveRestriction_rank_le_five :
    finrank k (LinearMap.range (primitiveRestriction k (zeroProjection k) (zeroInclusion k))) ≤ 5 := by
  rw [LagrangianPrimitiveRestrictionInjection.finrank_restriction_eq_primitive_span
    k (zeroProjection k) (zeroInclusion k) rfl]
  exact primitive_span_le_five k

end M9Native.LagrangianCommonKernelZero
