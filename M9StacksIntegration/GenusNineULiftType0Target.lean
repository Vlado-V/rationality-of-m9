module

public import M9StacksIntegration.PrimitiveNativeClassifierULiftRationalOpen
public import M9StacksIntegration.GenusNineCoarseVariety

@[expose] public section

/-! A concrete Type-0 coefficient binding of the independently chosen
actual genus-nine coarse target. Its variety property is derived from the
proved actual native properties. The remaining rational-open hypotheses
are genuine native integrality/density and classifier geometry. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
attribute [local instance] Space.pointTopology

namespace M9Native.GenusNineULiftType0Target

open M9StacksIntegration.AllTestNativeOriginalFunctor

variable (B : BigFppfSite.{0}) (hZ : B.Contains integerBase)
    (hC : B.Contains (Spec (.of ℂ)))

abbrev nativeTarget :=
  M9StacksIntegration.GenusNineCoarseOverField.genusNineCoarseSpace B hZ ℂ hC

/-- The canonical coefficient relabeling of the original independently
chosen actual genus-nine native target, on every original Type-0 test. -/
def target : M9StandaloneDraft.Space (ULift.{0} ℂ) :=
  PrimitiveNativeClassifierULiftRationalOpen.target B hC (nativeTarget B hZ hC)

/-- The exact original chosen presheaf is evaluated on canonically
inverse-relabeled tests; its physical native target is retained. -/
theorem target_obj :
    (target B hZ hC).obj =
      (Over.map ComplexULiftFunctionField.canonicalSpecIso.hom).op ⋙
        (originalPresheafFunctor ℂ B hC).obj (nativeTarget B hZ hC) := rfl

/-- The actual target variety property is a conclusion, not a supplied
geometric or finite-type premise. -/
theorem variety : M9StandaloneDraft.VarietySpace (ULift.{0} ℂ) (target B hZ hC) :=
  ComplexStandaloneCoefficientTransport.varietySpace _
    (GenusNineCoarseVariety.genusNine_variety B hZ ℂ hC)

/-- Actual local finite type is derived from the frozen chosen-target
properties. The native classifier criterion then yields a genuine common
dense affine open over the canonical Type-0 lifted coefficient field. -/
theorem rationalOpen (U : PrimitiveGrassmannianAction.space.Opens)
    (f : yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U) ⟶
      (nativeTarget B hZ hC).obj)
    (hInt : Space.IsIntegralSpace B (Spec (.of ℂ)) hC (nativeTarget B hZ hC).obj)
    (hf : DenseRange (Space.pointsMap B (Spec (.of ℂ)) hC
      (yoneda.obj (PrimitiveNativeDenseChartPresentation.parameterObject B hC U)) f))
    (h : PrimitiveNativeClassifierRationalOpen.ClassifierGeometry B hC (nativeTarget B hZ hC) U f) :
    M9StandaloneDraft.RationalOpen (ULift.{0} ℂ) 24 (target B hZ hC).obj :=
  PrimitiveNativeClassifierULiftRationalOpen.rationalOpen B hC (nativeTarget B hZ hC) U f hInt
    (GenusNineCoarseVariety.locallyFiniteType B hZ ℂ hC 9 (by decide)) hf h

end M9Native.GenusNineULiftType0Target
