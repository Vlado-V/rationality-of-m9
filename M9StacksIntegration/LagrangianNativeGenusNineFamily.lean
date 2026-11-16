module

public import M9StacksIntegration.LagrangianNativeSiteBounds
public import M9StacksIntegration.LagrangianGenusNine
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyOverField

/-! The original genus-nine family with derived site bounds.
The field-base structural maps and exact integer-base Over.map are retained.
No parameter/total containment, genus or classifying-map premise remains. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace M9Native.LagrangianNativeGenusNineFamily
open LagrangianLinearSections LagrangianLinearSectionGenericSmooth

universe u
variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))

/-- The original parameter-open structural map. -/
def baseProjection : (goodOpen K).toScheme ⟶ Spec (.of K) :=
  (goodOpen K).ι ≫ parameterProjection K

/-- The original native parameter base with containment proved. -/
def base : BigFppfOver B (Spec (.of K)) hK :=
  siteObject B (Spec (.of K)) hK (LagrangianNativeSiteBounds.contains_goodOpen K B hK)
    (baseProjection K)

/-- The original total with its actual coefficient map and proved bound. -/
def total : BigFppfOver B (Spec (.of K)) hK :=
  siteObject B (Spec (.of K)) hK (LagrangianNativeSiteBounds.contains_total K B hK)
    (restrictedProjection K ≫ baseProjection K)

/-- The original universal family as an actual native field-base arrow. -/
def projection : total K B hK ⟶ base K B hK :=
  Over.homMk (ObjectProperty.homMk (restrictedProjection K)) rfl

variable (hZ : B.Contains integerBase)

/-- The integer projection has the exact Over.map target required by
the actual chosen field-base-change classifier. -/
def integerProjection :
    (Over.map (integerSiteObject B hZ hK).hom).obj (total K B hK) ⟶
      (Over.map (integerSiteObject B hZ hK).hom).obj (base K B hK) :=
  (Over.map (integerSiteObject B hZ hK).hom).map (projection K B hK)

/-- The full all-original-field genus-nine condition for the same map. -/
theorem original_schemeCurve : M9StandaloneDraft.SchemeCurve
    ((BigFppfOver.toScheme B integerBase hZ).map (integerProjection K B hK hZ)) 9 := by
  change M9StandaloneDraft.SchemeCurve (restrictedProjection K) 9
  exact LagrangianGenusNine.original_schemeCurve K

/-- An actual native M9 object, with genus and containment derived. -/
def moduliObject : (moduliSmoothCurvesOfGenus B hZ 9).val.obj :=
  NativeSmoothGenusCurveClassifier.moduliObject B hZ (integerProjection K B hK hZ) 9
    (original_schemeCurve K B hK hZ)

/-- Its Cartesian native genus-nine classifier with exact source. -/
def classifyingMor : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ 9).val.p
    ((Over.map (integerSiteObject B hZ hK).hom).obj (base K B hK)) :=
  NativeSmoothGenusCurveClassifier.classifyingMor B hZ (integerProjection K B hK hZ) 9
    (original_schemeCurve K B hK hZ)

/-- Identity evaluation recovers the same original native family. -/
def classifiesOriginalFamily : (classifyingMor K B hK hZ).toFunctor.obj
    (Functor.FiberedMor.unit ((Over.map (integerSiteObject B hZ hK).hom).obj (base K B hK))) ≅
      moduliObject K B hK hZ :=
  NativeSmoothGenusCurveClassifier.classifiesOriginalFamily B hZ
    (integerProjection K B hK hZ) 9 (original_schemeCurve K B hK hZ)

/-- The constructed Bertini point preserves the original field. -/
theorem bertiniPoint_overBase :
    UniversalLagrangianNativeGenus.bertiniGoodPoint K ≫ baseProjection K = 𝟙 (Spec (.of K)) := by
  simp only [baseProjection, UniversalLagrangianNativeGenus.bertiniGoodPoint,
    ← Category.assoc, LagrangianConnectedPointCriterion.goodPoint_comp,
    SmoothIntegralHyperplaneCuts.parameterPoint_projection]

/-- An actual native point over the same original field, with no point
or coefficient-compatibility premise. -/
def bertiniPoint : siteObject B (Spec (.of K)) hK hK (𝟙 (Spec (.of K))) ⟶ base K B hK :=
  Over.homMk (ObjectProperty.homMk (UniversalLagrangianNativeGenus.bertiniGoodPoint K))
    (ObjectProperty.hom_ext _ (bertiniPoint_overBase K))

end M9Native.LagrangianNativeGenusNineFamily
