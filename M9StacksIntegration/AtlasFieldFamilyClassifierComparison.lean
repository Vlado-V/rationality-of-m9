module

public import StacksFrontier.AlgebraicGeometry.Quot.CurvesIsAlgebraic
public import M9StacksIntegration.CurveFieldClassifierComposition

/-! The original family recovered from an actual native atlas classifier.
The total space remains an algebraic space. Its field structure and its
classifier comparison are constructed from the actual functor at the unit,
with no supplied family identification or classifier smoothness premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor Deformation.Artin
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

universe u
namespace M9Native.AtlasFamilyClassifierComparison

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- Native Curves algebraicity is proved, not supplied by the atlas. -/
abbrev actualAlgebraicity := curvesFiberedCategory_isAlgebraicStack.{u,u+1} B hZ

/-- The original chosen two-fibre-product field stack of all curve families. -/
abbrev wholeStack := CurveFieldClassifyingFamily.fieldStack B hZ hK
  (actualAlgebraicity B hZ)

abbrev smallProjection := CurveFieldClassifyingFamily.smallProjection B hZ hK
  (actualAlgebraicity B hZ)
abbrev originalProjection := CurveFieldClassifyingFamily.originalProjection B hZ hK
  (actualAlgebraicity B hZ)

/-- The entire original projection retains the posted integer and field base square. -/
theorem originalProjection_comp_post :
    (originalProjection B hZ K hK ⋙ curvesProjectionOver B hZ) ⋙ Over.post B.inclusion =
      ((wholeStack B hZ K hK).val.val.p ⋙ Over.post B.inclusion) ⋙
        Over.map (B.inclusion.map (CurveFieldTargetComparison.baseArrow B hZ hK)) := by
  calc
    _ = smallProjection B hZ K hK ⋙
        ((curvesSmallBased B hZ).p ⋙ Over.post B.inclusion) := by
      simpa only [originalProjection,CurveFieldClassifyingFamily.originalProjection,smallProjection,
        curvesFiberedCategory,BasedCategory.ofFunctor,Functor.assoc]
        using congrArg
          (fun F => smallProjection B hZ K hK ⋙ (F ⋙ Over.post B.inclusion))
          (curvesSmallEquivalenceOver B hZ).inv.w
    _ = _ := Stack.algebraicStackBaseChangeProjection_comp
      B (Spec (.of K)) integerBase hK hZ
      (CurveFieldTargetComparison.baseArrow B hZ hK)
      (CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ))

local instance fieldFibered : (wholeStack B hZ K hK).val.val.p.IsFibered :=
  (wholeStack B hZ K hK).val.property.isFibered

/-- The same original curve family, including its algebraic-space total. -/
abbrev projectedCurveFamily (y : (wholeStack B hZ K hK).val.val.obj) : CurveFamily B hZ :=
  (originalProjection B hZ K hK).obj y

/-- The original integer base is the actual posted field base. -/
theorem projectedCurveFamily_integerBase (y : (wholeStack B hZ K hK).val.val.obj) :
    (projectedCurveFamily B hZ K hK y).base =
      (Over.map (CurveFieldTargetComparison.baseArrow B hZ hK)).obj
        ((wholeStack B hZ K hK).val.val.p.obj y) := by
  apply post_obj_injective
  have hi := congrArg (Over.post B.inclusion).obj
    (Functor.congr_obj (curvesSmallEquivalenceOver B hZ).inv.w
      ((smallProjection B hZ K hK).obj y))
  change (Over.post B.inclusion).obj (projectedCurveFamily B hZ K hK y).base =
    (((CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ)).val.val.p) ⋙
      Over.post B.inclusion).obj ((smallProjection B hZ K hK).obj y) at hi
  exact hi.trans (Functor.congr_obj
    (Stack.algebraicStackBaseChangeProjection_comp B (Spec (.of K)) integerBase hK hZ
      (CurveFieldTargetComparison.baseArrow B hZ hK)
      (CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ))) y)

/-- Its structural arrow retains the actual coefficient map to Spec K. -/
def projectedStructure (y : (wholeStack B hZ K hK).val.val.obj) :
    B.inclusion.obj (projectedCurveFamily B hZ K hK y).base.left ⟶ Spec (.of K) :=
  eqToHom (congrArg (fun T : BigFppfOver B integerBase hZ => B.inclusion.obj T.left)
    (projectedCurveFamily_integerBase B hZ K hK y)) ≫
      B.inclusion.map ((wholeStack B hZ K hK).val.val.p.obj y).hom

/-- The recovered family has the same literal object of the field site. -/
theorem projected_fieldBase (y : (wholeStack B hZ K hK).val.val.obj) :
    CurveFieldClassifyingFamily.fieldBase B hZ hK
      (projectedCurveFamily B hZ K hK y) (projectedStructure B hZ K hK y) =
      (wholeStack B hZ K hK).val.val.p.obj y := by
  apply post_obj_injective
  change Over.mk (projectedStructure B hZ K hK y) = _
  exact Over.mk_eqToHom_comp _ _

variable {V : BigFppfOver B (Spec (.of K)) hK}
  (a : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶ wholeStack B hZ K hK)

/-- Every actual native atlas morphism is its genuine fibre-preserving functor. -/
def nativeClassifier : FiberedMor (wholeStack B hZ K hK).val.val.p V where
  toBasedFunctor := a.hom.hom
  cartesian f := by
    have hw : a.hom.hom.toFunctor ⋙ (wholeStack B hZ K hK).val.val.p =
        Over.forget V := a.hom.hom.w
    have : (Over.forget V).IsHomLift f.left f :=
      IsHomLift.of_fac' (Over.forget V) f.left f rfl rfl rfl
    have hl := Functor.isHomLift_map_of_comp_eq hw f.left f
    exact (wholeStack B hZ K hK).val.property.isStronglyCartesian_homLift _ _

/-- The actual family at the identity object of the native atlas. -/
abbrev unitValue := (nativeClassifier B hZ K hK a).toFunctor.obj (FiberedMor.unit V)

/-- Its original family is constructed by the native projection. -/
abbrev family : CurveFamily B hZ := projectedCurveFamily B hZ K hK (unitValue B hZ K hK a)

abbrev structuralMap : B.inclusion.obj (family B hZ K hK a).base.left ⟶ Spec (.of K) :=
  projectedStructure B hZ K hK (unitValue B hZ K hK a)

/-- No identification of the atlas base is an input. -/
theorem family_fieldBase :
    CurveFieldClassifyingFamily.fieldBase B hZ hK
      (family B hZ K hK a) (structuralMap B hZ K hK a) = V :=
  (projected_fieldBase B hZ K hK (unitValue B hZ K hK a)).trans
    (nativeClassifier B hZ K hK a).obj_over_unit

/-- The original integer-base projection retains the actual coefficient arrow. -/
theorem family_integerBase :
    (family B hZ K hK a).base =
      (Over.map (CurveFieldTargetComparison.baseArrow B hZ hK)).obj V :=
  (projectedCurveFamily_integerBase B hZ K hK (unitValue B hZ K hK a)).trans
    (congrArg (Over.map (CurveFieldTargetComparison.baseArrow B hZ hK)).obj
      (nativeClassifier B hZ K hK a).obj_over_unit)

/-- The actual field-site isomorphism from the recovered family's base to the atlas. -/
def baseIso :
    CurveFieldClassifyingFamily.fieldBase B hZ hK
      (family B hZ K hK a) (structuralMap B hZ K hK a) ≅ V :=
  eqToIso (family_fieldBase B hZ K hK a)


/-- The original family reconstructed as an actual object of the field stack. -/
abbrev recoveredFieldFamily := CurveFieldClassifyingFamily.fieldFamily B hZ hK
  (actualAlgebraicity B hZ) (family B hZ K hK a) (structuralMap B hZ K hK a)

/-- The real hom-shrink counit compares the original small-family projections. -/
def recoverySmallIso :
    (smallProjection B hZ K hK).obj (recoveredFieldFamily B hZ K hK a) ≅
      (smallProjection B hZ K hK).obj (unitValue B hZ K hK a) :=
  (curvesSmallEquivalenceOver B hZ).counitIso.app
    ((smallProjection B hZ K hK).obj (unitValue B hZ K hK a))

/-- The literal base arrow, using only the derived equalities of native objects. -/
def recoveryBaseArrow :
    (wholeStack B hZ K hK).val.val.p.obj (recoveredFieldFamily B hZ K hK a) ⟶
      (wholeStack B hZ K hK).val.val.p.obj (unitValue B hZ K hK a) :=
  eqToHom (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK
    (actualAlgebraicity B hZ) (family B hZ K hK a) (structuralMap B hZ K hK a)) ≫
    (baseIso B hZ K hK a).hom ≫
      eqToHom (nativeClassifier B hZ K hK a).obj_over_unit.symm

/-- Native compatible-arrow lifting constructs the actual family recovery arrow. -/
theorem exists_recoveryArrow :
    ∃ β : recoveredFieldFamily B hZ K hK a ⟶ unitValue B hZ K hK a,
      (smallProjection B hZ K hK).map β = (recoverySmallIso B hZ K hK a).hom ∧
      (wholeStack B hZ K hK).val.val.p.map β = recoveryBaseArrow B hZ K hK a := by
  let e := recoverySmallIso B hZ K hK a
  let γ := recoveryBaseArrow B hZ K hK a
  have : (curvesSmallBased B hZ).p.IsHomLift
      (𝟙 ((curvesSmallBased B hZ).p.obj
        ((smallProjection B hZ K hK).obj (unitValue B hZ K hK a)))) e.hom := by
    simpa only [e,recoverySmallIso,smallProjection,recoveredFieldFamily,
      CurveFieldClassifyingFamily.fieldFamily_smallProjection,CurveFieldClassifyingFamily.smallFamily,
      family,projectedCurveFamily,originalProjection,CurveFieldClassifyingFamily.originalProjection,
      Functor.comp_obj,Iso.app_hom] using
      (curvesSmallEquivalenceOver B hZ).isHomLift_counitIso_hom_app
        ((smallProjection B hZ K hK).obj (unitValue B hZ K hK a))
  have hc :
      ((((CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ)).val.val.p) ⋙
          Over.post B.inclusion).map e.hom).left =
      eqToHom (congrArg Over.left (Functor.congr_obj
        (Stack.algebraicStackBaseChangeProjection_comp B (Spec (.of K)) integerBase hK hZ
          (CurveFieldTargetComparison.baseArrow B hZ hK)
          (CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ)))
        (recoveredFieldFamily B hZ K hK a))) ≫
      ((Over.post B.inclusion).map γ).left ≫
      eqToHom (congrArg Over.left (Functor.congr_obj
        (Stack.algebraicStackBaseChangeProjection_comp B (Spec (.of K)) integerBase hK hZ
          (CurveFieldTargetComparison.baseArrow B hZ hK)
          (CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ)))
        (unitValue B hZ K hK a))).symm := by
    change B.inclusion.map (((curvesSmallBased B hZ).p.map e.hom).left) = _
    rw [IsHomLift.fac' (curvesSmallBased B hZ).p
      (𝟙 ((curvesSmallBased B hZ).p.obj
        ((smallProjection B hZ K hK).obj (unitValue B hZ K hK a)))) e.hom]
    simp only [γ,recoveryBaseArrow,baseIso,eqToIso.hom,Over.post_map,Over.homMk_left,
      Over.eqToHom_left,eqToHom_map,Category.id_comp,eqToHom_trans]
  obtain ⟨β,hβ,hγ⟩ := Stack.liftsCompEqCompMap_algebraicStackBaseChangeProjection
    B (Spec (.of K)) integerBase hK hZ
    (CurveFieldTargetComparison.baseArrow B hZ hK)
    (CurveFieldTargetComparison.integerStack B hZ (actualAlgebraicity B hZ))
    e.hom ((Over.post B.inclusion).map γ) hc
  exact ⟨β,hβ,(Over.post B.inclusion).map_injective hγ⟩

/-- The recovery arrow is constructed, never supplied as a comparison premise. -/
def recoveryArrow : recoveredFieldFamily B hZ K hK a ⟶ unitValue B hZ K hK a :=
  (exists_recoveryArrow B hZ K hK a).choose

/-- Recovery preserves the actual coefficient structure. -/
theorem recoveryArrow_lift :
    (wholeStack B hZ K hK).val.val.p.IsHomLift (baseIso B hZ K hK a).hom
      (recoveryArrow B hZ K hK a) :=
  IsHomLift.of_fac' (wholeStack B hZ K hK).val.val.p
    (baseIso B hZ K hK a).hom (recoveryArrow B hZ K hK a)
    (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK
      (actualAlgebraicity B hZ) (family B hZ K hK a) (structuralMap B hZ K hK a))
    (nativeClassifier B hZ K hK a).obj_over_unit
    (exists_recoveryArrow B hZ K hK a).choose_spec.2

/-- Actual cartesianity follows from the genuine field CFG. -/
instance recoveryArrow_cartesian :
    (wholeStack B hZ K hK).val.val.p.IsStronglyCartesian (baseIso B hZ K hK a).hom
      (recoveryArrow B hZ K hK a) := by
  have := recoveryArrow_lift B hZ K hK a
  exact (wholeStack B hZ K hK).val.property.isStronglyCartesian_homLift _ _


/-- The canonical classifier of the actual unit value. -/
abbrev unitClassifier : FiberedMor (wholeStack B hZ K hK).val.val.p V :=
  FiberedMor.OfFiberObj.fiberedMor (wholeStack B hZ K hK).val.val.p V
    (nativeClassifier B hZ K hK a).obj_over_unit

local instance unitProjection_cartesian (x : Over V) :
    (wholeStack B hZ K hK).val.val.p.IsStronglyCartesian x.hom
      ((nativeClassifier B hZ K hK a).toFunctor.map (FiberedMor.toUnit x)) :=
  (FiberedMor.toUnit_left x) ▸ (nativeClassifier B hZ K hK a).cartesian (FiberedMor.toUnit x)

/-- Every atlas value is canonically the pullback of its actual unit family. -/
def unitComponentIso (x : Over V) :
    (unitClassifier B hZ K hK a).toFunctor.obj x ≅
      (nativeClassifier B hZ K hK a).toFunctor.obj x :=
  FiberedClassifierCartesianValue.valueIso (wholeStack B hZ K hK).val.val.p V
    (nativeClassifier B hZ K hK a).obj_over_unit x
    ((nativeClassifier B hZ K hK a).toFunctor.map (FiberedMor.toUnit x))

/-- The family-at-unit comparison is a genuine natural isomorphism. -/
def unitComparisonIso :
    (unitClassifier B hZ K hK a).toFunctor ≅
      (nativeClassifier B hZ K hK a).toFunctor :=
  NatIso.ofComponents (unitComponentIso B hZ K hK a) (by
    intro x y f
    have := (nativeClassifier B hZ K hK a).isHomLift_map f
    exact FiberedClassifierCartesianValue.valueIso_naturality
      (wholeStack B hZ K hK).val.val.p V
      (nativeClassifier B hZ K hK a).obj_over_unit f
      ((nativeClassifier B hZ K hK a).toFunctor.map (FiberedMor.toUnit x))
      ((nativeClassifier B hZ K hK a).toFunctor.map (FiberedMor.toUnit y))
      ((nativeClassifier B hZ K hK a).toFunctor.map f) (by
        rw [← Functor.map_comp,← FiberedMor.toUnit_comp]))

/-- Every component lies over the identity of the SAME native test base. -/
theorem unitComparisonIso_lift (x : Over V) :
    (wholeStack B hZ K hK).val.val.p.IsHomLift (𝟙 x.left)
      ((unitComparisonIso B hZ K hK a).hom.app x) :=
  FiberedClassifierCartesianValue.valueIso_hom_lift
    (wholeStack B hZ K hK).val.val.p V
    (nativeClassifier B hZ K hK a).obj_over_unit x
    ((nativeClassifier B hZ K hK a).toFunctor.map (FiberedMor.toUnit x))

/-- The same Yoneda comparison is based, preserving all coefficient maps. -/
def unitComparisonBasedIso :
    (unitClassifier B hZ K hK a).toBasedFunctor ≅
      (nativeClassifier B hZ K hK a).toBasedFunctor :=
  BasedNatIso.mkNatIso (unitComparisonIso B hZ K hK a)
    (unitComparisonIso_lift B hZ K hK a)

/-- The actual original family classifier agrees with the actual native
atlas map after the derived isomorphism of its original parameter base. -/
def comparisonBasedIso :
    BasedFunctor.comp
      (Stack.overMapBased B (Spec (.of K)) hK (baseIso B hZ K hK a).hom)
      (nativeClassifier B hZ K hK a).toBasedFunctor ≅
    (CurveFieldClassifyingFamily.classifyingMor B hZ hK (actualAlgebraicity B hZ)
      (family B hZ K hK a) (structuralMap B hZ K hK a)).toBasedFunctor :=
  by
    let b := Stack.overMapBased B (Spec (.of K)) hK (baseIso B hZ K hK a).hom
    have e : BasedFunctor.comp b (unitClassifier B hZ K hK a).toBasedFunctor ≅
        BasedFunctor.comp b (nativeClassifier B hZ K hK a).toBasedFunctor :=
      BasedNatIso.mkNatIso
        (isoWhiskerLeft (Over.map (baseIso B hZ K hK a).hom)
          (unitComparisonIso B hZ K hK a))
        (fun x => unitComparisonIso_lift B hZ K hK a
          ((Over.map (baseIso B hZ K hK a).hom).obj x))
    exact e.symm ≪≫
      FiberedClassifierBaseChange.comparisonBasedIso (wholeStack B hZ K hK).val.val.p
        (CurveFieldClassifyingFamily.fieldFamily_base B hZ hK (actualAlgebraicity B hZ)
          (family B hZ K hK a) (structuralMap B hZ K hK a))
        (nativeClassifier B hZ K hK a).obj_over_unit
        (baseIso B hZ K hK a).hom (recoveryArrow B hZ K hK a)

/-- The comparison is the genuine native two-isomorphism of stack maps. -/
def comparisonUnderlyingIso :
    (Stack.schemeStackMap.{u,u+1} B (Spec (.of K)) hK (baseIso B hZ K hK a).hom ≫ a).hom ≅
    (CurveFieldClassifyingFamily.stackMorphism B hZ hK (actualAlgebraicity B hZ)
      (family B hZ K hK a) (structuralMap B hZ K hK a)).hom :=
  Bicategory.InducedBicategory.isoMk (comparisonBasedIso B hZ K hK a)

/-- Smoothness of an actual atlas map gives smoothness of the literal
original-family classifier, through the DERIVED native comparison. -/
theorem classifier_isSmooth
    (ha : Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK a) :
    Stack.AlgebraicStacks.IsSmooth B (Spec (.of K)) hK
      (CurveFieldClassifyingFamily.stackMorphism B hZ hK (actualAlgebraicity B hZ)
        (family B hZ K hK a) (structuralMap B hZ K hK a)) := by
  apply CurveFieldClassifierComposition.isSmooth_of_underlyingIso B hK
    (comparisonUnderlyingIso B hZ K hK a)
  exact Stack.AlgebraicStacks.isSmooth_comp B (Spec (.of K)) hK _ _
    (Stack.isSmooth_schemeStackMap.{u,u+1} B (Spec (.of K)) hK
      (baseIso B hZ K hK a).hom (by infer_instance)) ha


/-- Integrality transfers along the proved equality of the original atlas base. -/
theorem family_isIntegral [IsIntegral (B.inclusion.obj V.left)] :
    IsIntegral (B.inclusion.obj (family B hZ K hK a).base.left) := by
  change IsIntegral (B.inclusion.obj (CurveFieldClassifyingFamily.fieldBase B hZ hK
    (family B hZ K hK a) (structuralMap B hZ K hK a)).left)
  rw [family_fieldBase]
  infer_instance

/-- Finite type belongs to the actual original structural map. -/
theorem family_locallyOfFiniteType [LocallyOfFiniteType (B.inclusion.map V.hom)] :
    LocallyOfFiniteType (structuralMap B hZ K hK a) := by
  change LocallyOfFiniteType (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
    (family B hZ K hK a) (structuralMap B hZ K hK a)).hom)
  rw [family_fieldBase]
  infer_instance

/-- The genuine atlas structural geometry transfers to this same family base. -/
theorem family_structural_properties
    [Smooth (B.inclusion.map V.hom)] [QuasiCompact (B.inclusion.map V.hom)] :
    Smooth (structuralMap B hZ K hK a) ∧
      QuasiCompact (structuralMap B hZ K hK a) ∧
      LocallyOfFiniteType (structuralMap B hZ K hK a) := by
  change Smooth (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (family B hZ K hK a) (structuralMap B hZ K hK a)).hom) ∧
    QuasiCompact (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (family B hZ K hK a) (structuralMap B hZ K hK a)).hom) ∧
    LocallyOfFiniteType (B.inclusion.map (CurveFieldClassifyingFamily.fieldBase B hZ hK
      (family B hZ K hK a) (structuralMap B hZ K hK a)).hom)
  rw [family_fieldBase]
  exact ⟨inferInstance,inferInstance,inferInstance⟩

end M9Native.AtlasFamilyClassifierComparison
