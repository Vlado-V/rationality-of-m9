module

public import M9StacksIntegration.SchematicCurveFibreConstants
public import M9StacksIntegration.NativeSchematicCurveClassifier
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesOfGenus
public import M9StacksIntegration.Private.CurveFamilyUniversalH0

/-!
# Actual schematic families in the genuine native genus substack

The original all-field scheme-curve predicate supplies the actual
geometric input. Native genus-substack membership, universal H0 and the
cartesian classifying functor are constructed from it, not supplied.
For the original universal LG family, its all-field genus-nine condition
must first be proved from the genuine connectedness, adjunction and
degree computations. This generic constructor does not prove those
remaining geometric statements.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
namespace M9Native.NativeSmoothGenusCurveClassifier
open CategoryTheory AlgebraicGeometry
open M9StacksIntegration.NativeSchematicCurveFamily
open M9StacksIntegration.AllTestNativeSchematicCharts

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The literal original schematic curve condition implies actual native
smooth-genus membership. In particular universal H0 is a conclusion,
obtained from the proved actual field-fibre constants maps. -/
theorem schemeCurveFamily_membership
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    IsSmoothH0FamilyOfFibreGenus B hZ g (schemeCurveFamily B hZ q g hq) := by
  let : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q) := hq.2.1
  refine ⟨⟨?_, ?_⟩, schemeCurveFamily_field_fibre_genus B hZ q g hq⟩
  · exact Space.isSmoothOfRelativeDimension_yoneda_map B integerBase hZ q 1
  · apply CurveFamilyUniversalH0.hasUniversallyBijectiveGlobalFunctions_of_fieldFibres
      B hZ (schemeCurveFamily B hZ q g hq)
    intro p
    exact SchematicCurveFibreConstants.field_fibre_globalFunctions_bijective B hZ q
      hq.1 hq.2.1 hq.2.2.1 p

/-- The original schematic family as an object of the actual native
moduli stack of smooth proper curves of genus g. -/
def moduliObject
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    (moduliSmoothCurvesOfGenus B hZ g).val.obj :=
  ⟨schemeCurveFamily B hZ q g hq, schemeCurveFamily_membership B hZ q g hq⟩

/-- The actual original schematic family has its cartesian classifying
functor to the actual native genus substack, without a classifier premise. -/
def classifyingMor
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p T := by
  let : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ g).2.isFibered
  exact Functor.FiberedMor.OfFiberObj.fiberedMor
    (moduliSmoothCurvesOfGenus B hZ g).val.p T
    (show (moduliSmoothCurvesOfGenus B hZ g).val.p.obj
      (moduliObject B hZ q g hq) = T from rfl)

/-- Evaluation over the identity recovers the same original family as
an object of the actual genus substack. -/
def classifiesOriginalFamily
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    (classifyingMor B hZ q g hq).toFunctor.obj (Functor.FiberedMor.unit T) ≅
      moduliObject B hZ q g hq := by
  let : (moduliSmoothCurvesOfGenus B hZ g).val.p.IsFibered :=
    (moduliSmoothCurvesOfGenus B hZ g).2.isFibered
  exact Functor.Fiber.fiberInclusion.mapIso
    (Functor.FiberedMor.OfFiberObj.fiberIso
      (moduliSmoothCurvesOfGenus B hZ g).val.p T
      (show (moduliSmoothCurvesOfGenus B hZ g).val.p.obj
        (moduliObject B hZ q g hq) = T from rfl)
      (classifyingMor B hZ q g hq).obj_over_unit)

end M9Native.NativeSmoothGenusCurveClassifier
