module

public import M9StacksIntegration.LagrangianTransverseRestriction
public import M9StacksIntegration.LagrangianPrimitiveRestrictionInjection
public import M9StacksIntegration.LagrangianGoodOpenRestriction
public import M9StacksIntegration.NonzeroSectionZeroFinite

/-!
# The actual original six sections on every genuine transverse five-cut

The original row matrix is surjective and its actual scheme-theoretic
section is integral and smooth of relative dimension one. The actual
primitive rank nine is derived by the geometric hyperplane ladder;
it is not supplied as an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

universe u

namespace M9Native.LagrangianTransverseSixSections

open LagrangianTransverseRestriction

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

section Transverse

variable (M : Matrix (Fin 5) (Fin 14) K)
  [IsIntegral (curve K M)] [SmoothOfRelativeDimension 1 (curveProjection K M)]

/-- Mukai II4.3 for the literal original transverse five-row section. -/
theorem sectionMap_injective (hM : Function.Surjective M.mulVec) : Function.Injective
    (LagrangianUniversalSections.sectionMap K (curveProjection K M) (inclusion K M)) := by
  apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
    K (curveProjection K M) (inclusion K M) rfl
  rw [primitiveRestriction_range_finrank K M hM]
  decide

theorem quotient_constantVector_ne_zero (hM : Function.Surjective M.mulVec)
    (v : Fin 6 → K) (hv : v ≠ 0) :
    (LagrangianUniversalSections.quotientMap K (inclusion K M)).app ⊤
      (LagrangianUniversalSections.constantVector K (curveProjection K M) v) ≠ 0 := by
  intro h
  have hz := (LagrangianUniversalSections.sectionMap_ker_iff
    K (curveProjection K M) (inclusion K M) v).mpr h
  exact hv ((sectionMap_injective K M hM) (hz.trans (map_zero _).symm))

end Transverse

open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

omit [IsAlgClosed K] [CharZero K] in
abbrev fibre (p : Spec (.of K) ⟶ parameter K) : Scheme.{u} :=
  pullback (familyProjection K) p

omit [IsAlgClosed K] [CharZero K] in
abbrev fibreProjection (p : Spec (.of K) ⟶ parameter K) : fibre K p ⟶ Spec (.of K) :=
  pullback.snd (familyProjection K) p

omit [IsAlgClosed K] [CharZero K] in
abbrev fibreToLG (p : Spec (.of K) ⟶ parameter K) : fibre K p ⟶ LagrangianGrassmannian.space K :=
  pullback.fst (familyProjection K) p ≫ familyToLG K

local instance fibreBundle_finiteLocallyFree (p : Spec (.of K) ⟶ parameter K) :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (LagrangianUniversalSections.bundle K (fibreToLG K p)) :=
  (LagrangianUniversalSections.quotient K (fibreToLG K p)).finiteLocallyFree.isFiniteLocallyFree

/-- Every actual original rational parameter in the good open has an
injective original six-section map; all curve and rank geometry is derived. -/
theorem goodOpen_sectionMap_injective (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _)
    (hg : p (IsLocalRing.closedPoint K) ∈ goodOpen K) :
    Function.Injective (LagrangianUniversalSections.sectionMap K (fibreProjection K p) (fibreToLG K p)) := by
  obtain ⟨M,hM,rfl,_,hr⟩ := LagrangianGoodOpenRestriction.every_parameter_restriction K p hp hg
  apply LagrangianPrimitiveRestrictionInjection.universal_sectionMap_injective_of_restriction_rank
    K _ _ (LagrangianOrderedFibre.geometricFibre_over K M hM)
  rw [hr]
  decide

theorem goodOpen_quotient_constantVector_ne_zero (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _)
    (hg : p (IsLocalRing.closedPoint K) ∈ goodOpen K)
    (v : Fin 6 → K) (hv : v ≠ 0) :
    (LagrangianUniversalSections.quotientMap K (fibreToLG K p)).app ⊤
      (LagrangianUniversalSections.constantVector K (fibreProjection K p) v) ≠ 0 := by
  intro h
  have hz := (LagrangianUniversalSections.sectionMap_ker_iff
    K (fibreProjection K p) (fibreToLG K p) v).mpr h
  exact hv ((goodOpen_sectionMap_injective K p hp hg) (hz.trans (map_zero _).symm))

/-- Full scheme-theoretic finiteness for every nonzero original section
on every actual good-open incidence fibre. Nilpotents are retained. -/
theorem goodOpen_zeroScheme_isFinite (p : Spec (.of K) ⟶ parameter K)
    (hp : p ≫ parameterProjection K = 𝟙 _)
    (hg : p (IsLocalRing.closedPoint K) ∈ goodOpen K)
    (v : Fin 6 → K) (hv : v ≠ 0) :
    IsFinite ((Stacks.Chow.zeroSchemeOfSection (fibre K p)
      (LagrangianUniversalSections.bundle K (fibreToLG K p))
      ((LagrangianUniversalSections.quotientMap K (fibreToLG K p)).app ⊤
        (LagrangianUniversalSections.constantVector K (fibreProjection K p) v))).subschemeι ≫
          fibreProjection K p) := by
  obtain ⟨M,hM,rfl⟩ := LagrangianParameterMatrix.exists_matrix K p hp
  letI : IsIntegral (fibre K (LagrangianMatrixPointRows.matrixPoint K M hM)) :=
    LagrangianGoodOpenRestriction.fibre_integral K M hM hg
  letI : SmoothOfRelativeDimension 1 (fibreProjection K (LagrangianMatrixPointRows.matrixPoint K M hM)) :=
    LagrangianGoodOpenRestriction.fibre_smooth K M hM hg
  letI : Smooth (fibreProjection K (LagrangianMatrixPointRows.matrixPoint K M hM)) :=
    SmoothOfRelativeDimension.smooth 1 _
  letI : IsCurve K (fibreProjection K (LagrangianMatrixPointRows.matrixPoint K M hM)) :=
    (isCurve_iff K _).mpr
      ⟨⟨⟩, topologicalKrullDim_eq_of_smoothOfRelativeDimension
        (fibreProjection K (LagrangianMatrixPointRows.matrixPoint K M hM)) 1⟩
  exact NonzeroSectionZeroFinite.isFinite_zeroSchemeOfSection_of_isCurve _ _ K _
    (goodOpen_quotient_constantVector_ne_zero K _ hp hg v hv)

end M9Native.LagrangianTransverseSixSections
