module

public import M9StacksIntegration.LagrangianChosenCoarseFamily
public import M9StacksIntegration.AllOriginalCoarseClassifierFibre
public import M9StacksIntegration.NativeSmoothGenusCoarseRecovery
public import M9StacksIntegration.NativeSmoothGenusClassifierCurveIso
public import M9StacksIntegration.SliceClassifierUnitIndexIso

/-! Equality under the actual chosen genus-nine coarse map gives an
isomorphism of the SAME original universal-family pullbacks over EVERY
original algebraically closed extension field. The simultaneous native
model, its identity-base source arrow, the actual original-family recovery,
and the physical isomorphism are all derived. No containment of the final
original field, source arrow, image equality or compatibility is an input. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.LagrangianChosenCoarseCurveIso

open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalPullbacks
  LagrangianLinearSectionGenericSmooth

universe u
variable (K : Type u) [Field K] [hKClosed : IsAlgClosed K] [hKZero : CharZero K]
  (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
  (hZ : B.Contains integerBase)
  (L : Type u) [Field L] [Algebra K L] [hLClosed : IsAlgClosed L]
  (x y : M9StandaloneDraft.FieldPoint K L ⟶
    (boundedInclusion B K hK).obj (LagrangianNativeGenusNineFamily.base K B hK))
  (hxy : LagrangianChosenCoarseFamily.pointValue K B hK hZ L x =
    LagrangianChosenCoarseFamily.pointValue K B hK hZ L y)

include hKClosed hKZero hLClosed hxy in
/-- Equal actual original chosen-coarse values give an actual physical
isomorphism of the original whole-family fibres over the SAME Spec L. -/
theorem exists_physicalIso :
    ∃ e : pullback (restrictedProjection K) x.left ≅
        pullback (restrictedProjection K) y.left,
      e.hom ≫ pullback.snd (restrictedProjection K) y.left =
        pullback.snd (restrictedProjection K) x.left := by
  have h9 : 2 ≤ (9 : ℕ) := by decide
  let U := LagrangianNativeGenusNineFamily.base K B hK
  let q := LagrangianNativeGenusNineFamily.integerProjection K B hK hZ
  let hq := LagrangianNativeGenusNineFamily.original_schemeCurve K B hK hZ
  let F := LagrangianNativeGenusNineFamily.classifyingMor K B hK hZ
  let A := LagrangianChosenCoarseFamily.fieldClassifier K B hK hZ
  let f := M9StacksIntegration.GenusNineCoarseOverField.coarseMap B hZ K hK 9 h9
  obtain ⟨Ω, hΩField, hΩClosed, hΩ, sΩ, a, b, v, α, hα, hx, hy⟩ :=
    AllOriginalCoarseClassifierFibre.exists_simultaneous_source_arrow K B hK f
      (M9StacksIntegration.GenusNineCoarseOverField.coarseMap_universalHomeomorphism
        B hZ K hK 9 h9) U U A A L x y hxy
  let : Field Ω := hΩField
  let Q := siteObject B (Spec (.of K)) hK hΩ sΩ
  let P := (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
    B hZ K hK 9 h9).val.val.p
  let e₀ := SliceClassifierUnitIndexIso.valueIso A a
  let e₁ := SliceClassifierUnitIndexIso.valueIso A b
  let β : A.obj (Over.mk a) ⟶ A.obj (Over.mk b) := e₀.inv ≫ α ≫ e₁.hom
  have hβ : P.IsHomLift (𝟙 Q) β := by
    have composeLift
        {X Y Z : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
          B hZ K hK 9 h9).val.val.obj}
        (r : X ⟶ Y) (s : Y ⟶ Z)
        (hr : P.IsHomLift (𝟙 Q) r) (hs : P.IsHomLift (𝟙 Q) s) :
        P.IsHomLift (𝟙 Q) (r ≫ s) :=
      IsHomLift.comp_lift_id_left P (𝟙 Q) s r
    have invertLift
        {X Y : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
          B hZ K hK 9 h9).val.val.obj}
        (e : X ≅ Y) (he : P.IsHomLift (𝟙 Q) e.hom) :
        P.IsHomLift (𝟙 Q) e.inv := IsHomLift.lift_id_inv P Q e
    have he₀ : P.IsHomLift (𝟙 Q) e₀.hom :=
      SliceClassifierUnitIndexIso.valueIso_hom_lift A a
    have he₁ : P.IsHomLift (𝟙 Q) e₁.hom :=
      SliceClassifierUnitIndexIso.valueIso_hom_lift A b
    exact composeLift _ _ (invertLift e₀ he₀) (composeLift _ _ hα he₁)
  let S := Over.map (NativeSmoothGenusCoarseClassifier.coefficientArrow B hZ K hK)
  let a₀ := S.map a
  let a₁ := S.map b
  let γ :
      ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).toFunctor.obj
        (Over.mk a₀)).obj ⟶
      ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).toFunctor.obj
        (Over.mk a₁)).obj :=
    NativeSmoothGenusCoarseRecovery.originalArrow B hZ K hK 9 h9
      U U Q F F a b β
  have hγ : (curvesProjectionOver B hZ).IsHomLift (𝟙 (S.obj Q)) γ :=
    NativeSmoothGenusCoarseRecovery.originalArrow_lift B hZ K hK 9 h9
      U U Q F F a b β hβ
  let w : Spec (.of L) ⟶ (BigFppfOver.toScheme B integerBase hZ).obj (S.obj Q) := v.left
  have hx' : w ≫ (BigFppfOver.toScheme B integerBase hZ).map a₀ = x.left :=
    congrArg (fun z => z.left) hx
  have hy' : w ≫ (BigFppfOver.toScheme B integerBase hZ).map a₁ = y.left :=
    congrArg (fun z => z.left) hy
  let e : pullback (restrictedProjection K) x.left ≅
      pullback (restrictedProjection K) y.left :=
    NativeSmoothGenusClassifierCurveIso.originalIso B hZ q q 9 hq hq a₀ a₁ γ hγ
      w x.left y.left hx' hy'
  have he : e.hom ≫ pullback.snd (restrictedProjection K) y.left =
      pullback.snd (restrictedProjection K) x.left :=
    NativeSmoothGenusClassifierCurveIso.originalIso_hom_snd
      B hZ q q 9 hq hq a₀ a₁ γ hγ w x.left y.left hx' hy'
  exact ⟨e, he⟩

/-- The physical original-fibre isomorphism under the actual chosen map. -/
def physicalIso : pullback (restrictedProjection K) x.left ≅
    pullback (restrictedProjection K) y.left :=
  (exists_physicalIso K B hK hZ L x y hxy).choose

/-- The physical isomorphism retains the SAME original field projection. -/
theorem physicalIso_hom_snd :
    (physicalIso K B hK hZ L x y hxy).hom ≫
        pullback.snd (restrictedProjection K) y.left =
      pullback.snd (restrictedProjection K) x.left :=
  (exists_physicalIso K B hK hZ L x y hxy).choose_spec

/-- The actual resulting isomorphism in the original category over Spec L. -/
def physicalOverIso :
    Over.mk (pullback.snd (restrictedProjection K) x.left) ≅
      Over.mk (pullback.snd (restrictedProjection K) y.left) :=
  Over.isoMk (physicalIso K B hK hZ L x y hxy)
    (physicalIso_hom_snd K B hK hZ L x y hxy)

end M9Native.LagrangianChosenCoarseCurveIso
