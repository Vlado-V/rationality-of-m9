module

public import M9StacksIntegration.StandaloneCurveCohomology
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.QuasiAffineClosedInFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothOfRelativeDimensionRepresentable

/-!
# Schematic curve families over arbitrary bounded bases

This construction uses actual relative dimension one, not a bound on the
dimension of the total scheme. Thus it applies to schematic families over
positive-dimensional test bases. Properness, finite presentation, flatness,
and relative dimension are transferred from the original scheme morphism.

The unchanged all-field-point standalone genus condition is an input only to
the last convenience definition. This file does not assume native genus-stack
membership, a classifier, or an equivalence of the family categories.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicGeometry

namespace M9StacksIntegration.NativeSchematicCurveFamily

universe u

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The genuine native family defined by a proper smooth relative curve over
an arbitrary bounded scheme base. No global total-dimension bound is used. -/
def properSmoothSchemeFamily {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T)
    (hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q))
    (hsmooth : SmoothOfRelativeDimension 1
      ((BigFppfOver.toScheme B integerBase hZ).map q)) : CurveFamily B hZ := by
  letI := hproper
  letI := hsmooth
  letI : Smooth ((BigFppfOver.toScheme B integerBase hZ).map q) :=
    SmoothOfRelativeDimension.smooth 1 _
  have hsm := Space.isSmoothOfRelativeDimension_yoneda_map B integerBase hZ q 1
  exact
    { base := T
      total := schemeSpace Z
      toBase := schemeSpaceMap q
      flat := Space.isFlat_of_isSmooth B integerBase hZ (yoneda.map q) hsm.1
      proper := Space.isProper_yoneda_map B integerBase hZ q hproper
      finitePresentation := Space.isFinitePresentation_yoneda_map B integerBase hZ q
        ⟨inferInstance, inferInstance, inferInstance⟩
      relativeDimensionLE := hsm.2.hasRelativeDimensionLE }

@[simp] theorem properSmoothSchemeFamily_base
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (hp hs) :
    (properSmoothSchemeFamily B hZ q hp hs).base = T := rfl

@[simp] theorem properSmoothSchemeFamily_total
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (hp hs) :
    (properSmoothSchemeFamily B hZ q hp hs).total = schemeSpace Z := rfl

@[simp] theorem properSmoothSchemeFamily_toBase
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (hp hs) :
    (properSmoothSchemeFamily B hZ q hp hs).toBase = schemeSpaceMap q := rfl

/-- An actual standalone scheme curve on a bounded scheme map has a native
curve-family object with exactly the same total scheme and base morphism. The
full all-field-point genus hypothesis is retained unchanged. -/
def schemeCurveFamily {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) : CurveFamily B hZ :=
  properSmoothSchemeFamily B hZ q hq.1 hq.2.1

@[simp] theorem schemeCurveFamily_base
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ) (hq) :
    (schemeCurveFamily B hZ q g hq).base = T := rfl

@[simp] theorem schemeCurveFamily_toBase
    {Z T : BigFppfOver B integerBase hZ} (q : Z ⟶ T) (g : ℕ) (hq) :
    (schemeCurveFamily B hZ q g hq).toBase = schemeSpaceMap q := rfl

end M9StacksIntegration.NativeSchematicCurveFamily
