module

public import M9StacksIntegration.NativeSchematicCurveClassifier
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison

/-! A genuine pullback of the original scheme maps gives the corresponding
cartesian arrow between their actual native curve families. Both original
maps are retained, rather than supplied by a family comparison premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
namespace M9Native.NativeSchematicCurveCartesianArrow

open M9StacksIntegration.NativeSchematicCurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {Z₀ T₀ Z₁ T₁ : BigFppfOver B integerBase hZ}
  (q₀ : Z₀ ⟶ T₀) (q₁ : Z₁ ⟶ T₁) (a : T₁ ⟶ T₀) (r : Z₁ ⟶ Z₀)
  (hp₀ : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q₀))
  (hs₀ : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q₀))
  (hp₁ : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q₁))
  (hs₁ : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q₁))
  (hPB : IsPullback
    ((BigFppfOver.toScheme B integerBase hZ).map r)
    ((BigFppfOver.toScheme B integerBase hZ).map q₁)
    ((BigFppfOver.toScheme B integerBase hZ).map q₀)
    ((BigFppfOver.toScheme B integerBase hZ).map a))

def arrow : properSmoothSchemeFamily B hZ q₁ hp₁ hs₁ ⟶
    properSmoothSchemeFamily B hZ q₀ hp₀ hs₀ where
  baseMap := a
  totalMap := schemeSpaceMap r
  cartesian := isPullback_schemeSpaceMap
    (IsPullback.of_map_of_faithful (BigFppfOver.toScheme B integerBase hZ) hPB)

theorem arrow_baseMap :
    (arrow B hZ q₀ q₁ a r hp₀ hs₀ hp₁ hs₁ hPB).baseMap = a := rfl

theorem arrow_totalMap :
    (arrow B hZ q₀ q₁ a r hp₀ hs₀ hp₁ hs₁ hPB).totalMap = schemeSpaceMap r := rfl

include hPB in
theorem arrow_cartesian : IsPullback (schemeSpaceMap r) (schemeSpaceMap q₁)
    (schemeSpaceMap q₀) (schemeSpaceMap a) :=
  isPullback_schemeSpaceMap
    (IsPullback.of_map_of_faithful (BigFppfOver.toScheme B integerBase hZ) hPB)

theorem arrow_isStronglyCartesian :
    (curvesProjectionOver B hZ).IsStronglyCartesian a
      (arrow B hZ q₀ q₁ a r hp₀ hs₀ hp₁ hs₁ hPB) := by
  let f := arrow B hZ q₀ q₁ a r hp₀ hs₀ hp₁ hs₁ hPB
  have : (curvesProjectionOver B hZ).IsHomLift a f := Functor.IsHomLift.map f
  have hfib : (curvesProjectionOver B hZ).IsFiberedInGroupoids :=
    (curvesFiberedCategory B hZ).property
  exact hfib.isStronglyCartesian_homLift a f

end M9Native.NativeSchematicCurveCartesianArrow
