module

public import M9StacksIntegration.LagrangianDegreeSixteen
public import M9StacksIntegration.UniversalLagrangianFieldGenus
public import M9StacksIntegration.LagrangianBertiniRestrictionKernel

/-!
# The original universal section family in the genuine genus-nine stack

The numerical LG degree theorem and the proved original genus-degree
relations give the actual genus nine. The native moduli object and
Cartesian classifier retain the literal original universal family.
The original fourteen-section map is transported by the proved actual
canonical-line isomorphism, and the existing canonical completeness
theorem is applied with the resulting genuine genus.

This does not prove a coarse-moduli or rationality theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace M9Native.LagrangianGenusNine
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth
open SmoothIntegralHyperplaneCuts

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]

/-- The actual original constructed five-cut curve has genus nine. -/
theorem fiveCut_genus_eq_nine :
    genus (LagrangianFiveCutCanonical.structureMap K) = 9 := by
  have h := LagrangianFiveCutCanonical.genus_degree_relation K
  rw [LagrangianActualDegree.degreeWithRespectTo_determinant_eq_sixteen K] at h
  omega

/-- The actual computed genus of the original universal family is nine. -/
theorem family_genus_eq_nine : UniversalLagrangianNativeGenus.fibreGenus K = 9 := by
  rw [UniversalLagrangianNativeGenus.fibreGenus_eq_fiveCut_genus K]
  exact fiveCut_genus_eq_nine K

/-- Every actual field-valued fibre, including nonclosed points and
arbitrary coefficient fields, has native genus nine. -/
theorem field_fibre_genus_eq_nine
    {L : Type u} [Field L] (p : Spec (.of L) ⟶ (goodOpen K).toScheme) :
    genus (pullback.snd (restrictedProjection K) p) = 9 :=
  (UniversalLagrangianFieldGenus.field_genus_eq_fibreGenus K p).trans
    (family_genus_eq_nine K)

/-- The unchanged original restricted projection satisfies the full
original all-field genus-nine curve condition. -/
theorem original_schemeCurve : M9StandaloneDraft.SchemeCurve (restrictedProjection K) 9 := by
  simpa only [family_genus_eq_nine K] using
    UniversalLagrangianNativeGenus.original_schemeCurve K

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- Membership in the true native genus-nine curve substack is proved
for the literal original universal family. -/
theorem family_membership
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    IsSmoothH0FamilyOfFibreGenus B hZ 9
      (UniversalLagrangianCurveFamily.family B hZ K hU hV) := by
  simpa only [family_genus_eq_nine K] using
    UniversalLagrangianNativeGenus.family_membership K B hZ hU hV

/-- The actual original family as an object of the genuine native M9. -/
def moduliObject
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    (moduliSmoothCurvesOfGenus B hZ 9).val.obj :=
  ⟨UniversalLagrangianCurveFamily.family B hZ K hU hV,
    family_membership K B hZ hU hV⟩

/-- The genuine Cartesian genus-nine classifier of the original family. -/
def classifyingMor
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ 9).val.p
      (UniversalLagrangianCurveFamily.family B hZ K hU hV).base := by
  let : (moduliSmoothCurvesOfGenus B hZ 9).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ 9).2.isFibered
  exact Functor.FiberedMor.OfFiberObj.fiberedMor
    (moduliSmoothCurvesOfGenus B hZ 9).val.p
    (UniversalLagrangianCurveFamily.family B hZ K hU hV).base
    (show (moduliSmoothCurvesOfGenus B hZ 9).val.p.obj
      (moduliObject K B hZ hU hV) = _ from rfl)

/-- Identity evaluation recovers the same original family in native M9. -/
def classifiesOriginalFamily
    (hU : B.Contains (goodOpen K).toScheme)
    (hV : B.Contains ((familyProjection K) ⁻¹ᵁ goodOpen K).toScheme) :
    (classifyingMor K B hZ hU hV).toFunctor.obj
      (Functor.FiberedMor.unit (UniversalLagrangianCurveFamily.family B hZ K hU hV).base) ≅
      moduliObject K B hZ hU hV := by
  let : (moduliSmoothCurvesOfGenus B hZ 9).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ 9).2.isFibered
  exact Functor.Fiber.fiberInclusion.mapIso
    (Functor.FiberedMor.OfFiberObj.fiberIso
      (moduliSmoothCurvesOfGenus B hZ 9).val.p
      (UniversalLagrangianCurveFamily.family B hZ K hU hV).base
      (show (moduliSmoothCurvesOfGenus B hZ 9).val.p.obj
        (moduliObject K B hZ hU hV) = _ from rfl)
      (classifyingMor K B hZ hU hV).obj_over_unit)

/-- The literal original primitive sections, transported to the actual
native canonical line by its proved original-line isomorphism. -/
abbrev canonicalRestriction :
    (Fin 14 → K) →ₗ[K]
      cohomologyOverField K (LagrangianFiveCutCanonical.structureMap K)
        (Stacks.Duality.dualizingSheafOverField (LagrangianFiveCutCanonical.structureMap K)) 0 :=
  LagrangianPrimitiveRestriction.canonicalRestriction K
    (LagrangianFiveCutCanonical.structureMap K) (fiveCutToLG K)
    (LagrangianFiveCutCanonical.canonicalIsoCurveLine K).symm

/-- Canonical completeness of the original fourteen sections, with no
canonical-line or genus premise remaining. -/
theorem canonicalRestriction_surjective : Function.Surjective (canonicalRestriction K) :=
  LagrangianBertiniRestrictionKernel.fiveCut_canonicalRestriction_surjective K
    (LagrangianFiveCutCanonical.canonicalIsoCurveLine K).symm (fiveCut_genus_eq_nine K)

/-- The actual native canonical section space has dimension nine. -/
theorem canonicalH0_finrank :
    finrank K (cohomologyOverField K (LagrangianFiveCutCanonical.structureMap K)
      (Stacks.Duality.dualizingSheafOverField (LagrangianFiveCutCanonical.structureMap K)) 0) = 9 := by
  let : IsIntegral (fiveCutCurve K) := fiveCutCurve_integral K
  let : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
      (LagrangianFiveCutCanonical.structureMap K).appTop) :=
    isIso_globalSections_of_isAlgClosed K (LagrangianFiveCutCanonical.structureMap K)
  exact (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField
    (LagrangianFiveCutCanonical.structureMap K) (fiveCutCurve_dimension K).le).trans
      (fiveCut_genus_eq_nine K)

end M9Native.LagrangianGenusNine
