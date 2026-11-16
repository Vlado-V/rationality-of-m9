module

public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier

/-! Recovery of ANY original native genus classifier through the actual
chosen field stack. The real hom-shrink unit is vertical by its proved
EquivalenceOver laws and the original classifier's basedness. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeSmoothGenusCoarseRecovery

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (g : ℕ) (hg : 2 ≤ g)

/-- The actual hom-shrink unit recovers ANY specified original genus
classifier, on every original slice object. -/
def originalValueIso (U : BigFppfOver B (Spec (.of K)) hK)
    (F : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p
      ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj U))
    (x : Over U) :
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).obj
        ((NativeSmoothGenusCoarseClassifier.liftOriginalClassifier
          B hZ K hK U g hg F).obj x) ≅
      (F.toFunctor.obj ((Over.post (Over.map
        (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj x)).obj :=
  ((curvesSmallEquivalenceOver B hZ).unitIso.app
    (F.toFunctor.obj ((Over.post (Over.map
      (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj x)).obj).symm

/-- The recovery is over the identity of the SAME original base; no
base or scalar compatibility is supplied as a premise. -/
theorem originalValueIso_lift (U : BigFppfOver B (Spec (.of K)) hK)
    (F : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p
      ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj U))
    (x : Over U) :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj x.left))
      (originalValueIso B hZ K hK g hg U F x).hom := by
  let y := (Over.post (Over.map
    (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj x
  let X := (F.toFunctor.obj y).obj
  have hx : (curvesProjectionOver B hZ).obj X =
      (Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj x.left :=
    Functor.congr_obj F.w y
  have h := (curvesSmallEquivalenceOver B hZ).isHomLift_unitIso_inv_app X
  change (curvesProjectionOver B hZ).IsHomLift
    (𝟙 ((curvesProjectionOver B hZ).obj X))
    ((curvesSmallEquivalenceOver B hZ).unitIso.inv.app X) at h
  rw [hx] at h
  exact h

variable (U V Q : BigFppfOver B (Spec (.of K)) hK)
  (F : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p
    ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj U))
  (G : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p
    ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj V))
  (a : Q ⟶ U) (b : Q ⟶ V)
  (α : (NativeSmoothGenusCoarseClassifier.liftOriginalClassifier B hZ K hK U g hg F).obj
      (Over.mk a) ⟶
    (NativeSmoothGenusCoarseClassifier.liftOriginalClassifier B hZ K hK V g hg G).obj
      (Over.mk b))

/-- Project and conjugate a genuine chosen-source arrow into an arrow
between the SAME specified original genus classifiers. -/
def originalArrow :
    (F.toFunctor.obj ((Over.post (Over.map
      (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj (Over.mk a))).obj ⟶
    (G.toFunctor.obj ((Over.post (Over.map
      (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK))).obj (Over.mk b))).obj :=
  (originalValueIso B hZ K hK g hg U F (Over.mk a)).inv ≫
    (NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map α ≫
      (originalValueIso B hZ K hK g hg V G (Over.mk b)).hom

/-- ANY vertical chosen-source arrow gives a vertical original-family
arrow after the derived actual recovery. -/
theorem originalArrow_lift
    (hα : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
      B hZ K hK g hg).val.val.p.IsHomLift (𝟙 Q) α) :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      (originalArrow B hZ K hK g hg U V Q F G a b α) := by
  have hF : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      (originalValueIso B hZ K hK g hg U F (Over.mk a)).hom :=
    originalValueIso_lift B hZ K hK g hg U F (Over.mk a)
  have hG : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      (originalValueIso B hZ K hK g hg V G (Over.mk b)).hom :=
    originalValueIso_lift B hZ K hK g hg V G (Over.mk b)
  have hproj : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map α) :=
    NativeSmoothGenusCoarseClassifier.original_isHomLift_id B hZ K hK g hg Q α hα
  have : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      (originalValueIso B hZ K hK g hg U F (Over.mk a)).inv := inferInstance
  have : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)).obj Q))
      ((NativeSmoothGenusCoarseClassifier.originalProjection B hZ K hK g hg).map α ≫
        (originalValueIso B hZ K hK g hg V G (Over.mk b)).hom) :=
    IsHomLift.comp_lift_id_left _ _ _ _
  exact IsHomLift.comp_lift_id_left _ _ _ _

end M9Native.NativeSmoothGenusCoarseRecovery
