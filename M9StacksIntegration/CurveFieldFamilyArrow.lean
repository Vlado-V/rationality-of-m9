module

public import M9StacksIntegration.CurveFieldClassifyingFamily

/-!
# Lifting the original curve-family arrows to the actual field base

The input is the original cartesian family arrow and its literal ground
structure square. The output is an arrow in the genuine native base
change, whose small-model projection and original base arrow are proved.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Deformation.Artin
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u
namespace M9Native.CurveFieldFamilyArrow

open CurveFieldClassifyingFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {K : Type u} [Field K] (hK : B.Contains (Spec (.of K)))
  (hAlg : Stack.IsAlgebraicStack.{u,u+1} B integerBase hZ
    (curvesFiberedCategory B hZ).val)
  {Q R : CurveFamily B hZ}
  (sQ : B.inclusion.obj Q.base.left ⟶ Spec (.of K))
  (sR : B.inclusion.obj R.base.left ⟶ Spec (.of K))
  (β : Q ⟶ R) (hβ : B.inclusion.map β.baseMap.left ≫ sR = sQ)

/-- The original base arrow, with its actual ground-field compatibility. -/
def baseArrow : fieldBase B hZ hK Q sQ ⟶ fieldBase B hZ hK R sR :=
  Over.homMk β.baseMap.left (by
    apply B.inclusion.map_injective
    exact hβ)

/-- Its underlying scheme map is the original given base map. -/
theorem baseArrow_left :
    B.inclusion.map (baseArrow B hZ hK sQ sR β hβ).left =
      B.inclusion.map β.baseMap.left := rfl

/-- The same arrow on the literal projected bases of the constructed objects. -/
def projectedBaseArrow :
    (fieldStack B hZ hK hAlg).val.val.p.obj (fieldFamily B hZ hK hAlg Q sQ) ⟶
      (fieldStack B hZ hK hAlg).val.val.p.obj (fieldFamily B hZ hK hAlg R sR) :=
  eqToHom (fieldFamily_base B hZ hK hAlg Q sQ) ≫
    baseArrow B hZ hK sQ sR β hβ ≫
    eqToHom (fieldFamily_base B hZ hK hAlg R sR).symm

/-- The native small-model arrow retains the original integer-base map. -/
theorem small_map_base :
    (curvesSmallBased B hZ).p.map ((curvesSmallEquivalenceOver B hZ).hom.functor.map β) =
      β.baseMap := by
  have h := Functor.congr_hom (curvesSmallEquivalenceOver B hZ).hom.w β
  simpa only [curvesFiberedCategory, BasedCategory.ofFunctor, curvesProjectionOver,
    Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id] using h

/-- The real native base-change lifting theorem applies to the given
original family arrow and the proved actual ground-base square. -/
theorem exists_arrow :
    ∃ α : fieldFamily B hZ hK hAlg Q sQ ⟶ fieldFamily B hZ hK hAlg R sR,
      (smallProjection B hZ hK hAlg).map α =
        (curvesSmallEquivalenceOver B hZ).hom.functor.map β ∧
      (fieldStack B hZ hK hAlg).val.val.p.map α =
        projectedBaseArrow B hZ hK hAlg sQ sR β hβ := by
  let γ := projectedBaseArrow B hZ hK hAlg sQ sR β hβ
  have hc :
      (((CurveFieldTargetComparison.integerStack B hZ hAlg).val.val.p ⋙
          Over.post B.inclusion).map
        ((curvesSmallEquivalenceOver B hZ).hom.functor.map β)).left =
      eqToHom (congrArg Over.left (Functor.congr_obj
        (Stack.algebraicStackBaseChangeProjection_comp B (Spec (.of K)) integerBase hK hZ
          (CurveFieldTargetComparison.baseArrow B hZ hK)
          (CurveFieldTargetComparison.integerStack B hZ hAlg))
        (fieldFamily B hZ hK hAlg Q sQ))) ≫
      ((Over.post B.inclusion).map γ).left ≫
      eqToHom (congrArg Over.left (Functor.congr_obj
        (Stack.algebraicStackBaseChangeProjection_comp B (Spec (.of K)) integerBase hK hZ
          (CurveFieldTargetComparison.baseArrow B hZ hK)
          (CurveFieldTargetComparison.integerStack B hZ hAlg))
        (fieldFamily B hZ hK hAlg R sR))).symm := by
    change B.inclusion.map
      (((curvesSmallBased B hZ).p.map
        ((curvesSmallEquivalenceOver B hZ).hom.functor.map β)).left) = _
    rw [small_map_base B hZ β]
    simp only [γ, projectedBaseArrow, Over.post_map, eqToHom_refl,
      Category.id_comp, Category.comp_id]
    rfl
  obtain ⟨α, hα, hγ⟩ :=
    Stack.liftsCompEqCompMap_algebraicStackBaseChangeProjection B (Spec (.of K)) integerBase
      hK hZ (CurveFieldTargetComparison.baseArrow B hZ hK)
      (CurveFieldTargetComparison.integerStack B hZ hAlg)
      ((curvesSmallEquivalenceOver B hZ).hom.functor.map β)
      ((Over.post B.inclusion).map γ) hc
  refine ⟨α, hα, ?_⟩
  exact (Over.post B.inclusion).map_injective hγ

/-- The actual lifted arrow, obtained from the original native universal property. -/
def arrow : fieldFamily B hZ hK hAlg Q sQ ⟶ fieldFamily B hZ hK hAlg R sR :=
  (exists_arrow B hZ hK hAlg sQ sR β hβ).choose

/-- Its projection is exactly the original small-model arrow. -/
theorem arrow_smallProjection :
    (smallProjection B hZ hK hAlg).map (arrow B hZ hK hAlg sQ sR β hβ) =
      (curvesSmallEquivalenceOver B hZ).hom.functor.map β :=
  (exists_arrow B hZ hK hAlg sQ sR β hβ).choose_spec.1

/-- Its base map is the given original map, with only the proved object identifications. -/
theorem arrow_base :
    (fieldStack B hZ hK hAlg).val.val.p.map (arrow B hZ hK hAlg sQ sR β hβ) =
      projectedBaseArrow B hZ hK hAlg sQ sR β hβ :=
  (exists_arrow B hZ hK hAlg sQ sR β hβ).choose_spec.2

/-- The lift lies over the literal original ground-base arrow. -/
theorem arrow_isHomLift :
    (fieldStack B hZ hK hAlg).val.val.p.IsHomLift
      (baseArrow B hZ hK sQ sR β hβ) (arrow B hZ hK hAlg sQ sR β hβ) :=
  IsHomLift.of_fac' (fieldStack B hZ hK hAlg).val.val.p
    (baseArrow B hZ hK sQ sR β hβ) (arrow B hZ hK hAlg sQ sR β hβ)
    (fieldFamily_base B hZ hK hAlg Q sQ) (fieldFamily_base B hZ hK hAlg R sR)
    (arrow_base B hZ hK hAlg sQ sR β hβ)

/-- It is genuinely cartesian in the actual field-based curve category. -/
theorem arrow_isStronglyCartesian :
    (fieldStack B hZ hK hAlg).val.val.p.IsStronglyCartesian
      (baseArrow B hZ hK sQ sR β hβ) (arrow B hZ hK hAlg sQ sR β hβ) := by
  have := arrow_isHomLift B hZ hK hAlg sQ sR β hβ
  exact Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift
    (fieldStack B hZ hK hAlg).val.property
    (baseArrow B hZ hK sQ sR β hβ) (arrow B hZ hK hAlg sQ sR β hβ)

end M9Native.CurveFieldFamilyArrow
