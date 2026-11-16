module

public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier
public import M9StacksIntegration.StrictPullbackOriginalArrow
public import M9StacksIntegration.ClassifierUnitArrowReflection

/-! Fullness on the actual chosen field-base smooth-genus source.
An original curve-family arrow over the identity lifts through the full
smooth-open inclusion and the actual hom-shrink inverse, then through
the strict pullback with its exact original field-base object. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 200000
set_option maxRecDepth 512

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeSmoothGenusSourceFullness

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (g : ℕ) (hg : 2 ≤ g)

abbrev integerProjection :
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.obj ⥤
      CurveFamily B hZ :=
  (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property.ι ⋙
    (curvesSmallEquivalenceOver B hZ).inv.functor

def integerProjection_fullyFaithful :
    (integerProjection B hZ g hg).FullyFaithful :=
  (Functor.FullyFaithful.ofFullyFaithful
    (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property.ι).comp
    (curvesSmallEquivalenceOver B hZ).toEquivalence.fullyFaithfulInverse

theorem integerProjection_comp :
    integerProjection B hZ g hg ⋙ curvesProjectionOver B hZ =
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p := by
  have hi : (curvesSmallEquivalenceOver B hZ).inv.functor ⋙ curvesProjectionOver B hZ =
      (curvesSmallBased B hZ).p := (curvesSmallEquivalenceOver B hZ).inv.w
  change (_ ⋙ _) ⋙ _ = _
  rw [Functor.assoc, hi]
  rfl

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (T : BigFppfOver B (Spec (.of K)) hK)
  {x y : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj}
  (hx : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj x = T)
  (hy : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.obj y = T)
  (α : (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj x ⟶
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj y)
  (hα : (curvesProjectionOver B hZ).IsHomLift
    (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj T)) α)

/-- A raw original curve arrow lifts to the ACTUAL chosen field source.
Only the specified endpoint bases and the actual raw arrow are inputs. -/
def liftRawArrow : x ⟶ y :=
  StrictPullbackOriginalArrow.liftArrow
    (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p
    (integerProjection B hZ g hg) (curvesProjectionOver B hZ)
    (integerProjection_fullyFaithful B hZ g hg) (integerProjection_comp B hZ g hg)
    T hx hy α hα

/-- The entire specified original family arrow is recovered exactly. -/
theorem liftRawArrow_original :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map
      (liftRawArrow B hZ g hg K hK T hx hy α hα) = α :=
  StrictPullbackOriginalArrow.liftArrow_original
    (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p
    (integerProjection B hZ g hg) (curvesProjectionOver B hZ)
    (integerProjection_fullyFaithful B hZ g hg) (integerProjection_comp B hZ g hg)
    T hx hy α hα

/-- This is an arrow over id T; the coefficient field is fixed. -/
theorem liftRawArrow_isHomLift :
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p.IsHomLift
      (𝟙 T) (liftRawArrow B hZ g hg K hK T hx hy α hα) :=
  StrictPullbackOriginalArrow.liftArrow_isHomLift
    (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p
    (integerProjection B hZ g hg) (curvesProjectionOver B hZ)
    (integerProjection_fullyFaithful B hZ g hg) (integerProjection_comp B hZ g hg)
    T hx hy α hα

omit hx hy α hα in
/-- At the actual Yoneda unit, a raw family arrow is enough to force
literal equality of the maps to the EXACT chosen coarse algebraic space. -/
theorem coarseMap_eq_of_raw_unit_arrow
    {F G : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val}
    (β : (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
        (F.obj (Functor.FiberedMor.unit T)) ⟶
      (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
        (G.obj (Functor.FiberedMor.unit T)))
    (hβ : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj T)) β) :
    AlgebraicSpaceValuedClassifierReflection.nativeMap B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom F =
      AlgebraicSpaceValuedClassifierReflection.nativeMap B (Spec (.of K)) hK
        (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom G := by
  have hF : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
      B hZ K hK g hg).val.val.p.obj (F.obj (Functor.FiberedMor.unit T)) = T :=
    Functor.congr_obj F.w (Functor.FiberedMor.unit T)
  have hG : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
      B hZ K hK g hg).val.val.p.obj (G.obj (Functor.FiberedMor.unit T)) = T :=
    Functor.congr_obj G.w (Functor.FiberedMor.unit T)
  exact ClassifierUnitArrowReflection.nativeMap_eq_of_unit_arrow B (Spec (.of K)) hK
    (M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK g hg).hom.hom
    (liftRawArrow B hZ g hg K hK T hF hG β hβ)
    (liftRawArrow_isHomLift B hZ g hg K hK T hF hG β hβ)

end M9Native.NativeSmoothGenusSourceFullness
