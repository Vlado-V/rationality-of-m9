module

public import M9StacksIntegration.StackChangeOfBaseClassifier
public import M9StacksIntegration.NativeSmoothGenusCurveClassifier
public import M9StacksIntegration.GenusFieldSmallComparison
public import M9StacksIntegration.GenusNineCoarseOverField

/-! The actual schematic genus classifier in the chosen native smooth-genus
stack over the coefficient field. The target is the literal
GenusNineCoarseOverField.smoothStack, constructed from proved native
algebraicity and finite inertia. No source equivalence, classifier
compatibility, or coarse invariance is assumed. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9Native.NativeSmoothGenusCoarseClassifier

universe u
variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- The actual field-genus condition gives the native cohomological genus
condition defining the chosen smooth open. -/
theorem cohomological_of_fieldGenus (g : ℕ) {F : CurveFamily B hZ}
    (hF : IsSmoothH0FamilyOfFibreGenus B hZ g F) :
    IsSmoothH0Family B hZ F ∧ CurveFamily.HasGenus B hZ F g :=
  ⟨hF.1, (F.hasFieldPointFibreGenus_iff_hasGenus_of_bijective_algebraMap_fibre
    (CurveFamily.bijective_algebraMap_fibre_of_hasUniversallyBijectiveGlobalFunctions
      hF.1.2) g).mp hF.2⟩

/-- The TRUE native genus objects map to the actual chosen smooth open,
through the genuine hom-shrink functor. Membership is derived. -/
def integerComparison (g : ℕ) (hg : 2 ≤ g) :
    (moduliSmoothCurvesOfGenus B hZ g).val ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val where
  toFunctor :=
    { obj X := ⟨(curvesSmallEquivalenceOver B hZ).hom.functor.obj X.obj,
        (curvesSmallOpenSubstack_property_iff B hZ
          (curvesFiberedCategory_isAlgebraicStack.{u, u + 1} B hZ)
          (isOpenCurvesLocus_isSmoothH0Family_and_hasGenus_of_h2_h3 B hZ g
            CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.1
            CurveFamily.firstHigherDirectImage_of_hasResidueFieldGlobalFunctions.2)
          X.obj).mpr (cohomological_of_fieldGenus B hZ g X.property)⟩
      map a := ObjectProperty.homMk
        ((curvesSmallEquivalenceOver B hZ).hom.functor.map a.hom)
      map_id X := by
        apply ObjectProperty.hom_ext
        exact (curvesSmallEquivalenceOver B hZ).hom.functor.map_id X.obj
      map_comp a b := by
        apply ObjectProperty.hom_ext
        exact (curvesSmallEquivalenceOver B hZ).hom.functor.map_comp a.hom b.hom }
  w := by
    have h := (curvesSmallEquivalenceOver B hZ).hom.w
    change ((GenusFieldSmallComparison.genusProperty B hZ g).ι ⋙
      (curvesSmallEquivalenceOver B hZ).hom.functor) ⋙
        (curvesSmallBased B hZ).p =
      (GenusFieldSmallComparison.genusProperty B hZ g).ι ⋙ curvesProjectionOver B hZ
    rw [Functor.assoc, h]
    rfl

/-- The actual original object and the entire family arrow are retained. -/
theorem integerComparison_obj (g : ℕ) (hg : 2 ≤ g)
    (X : (moduliSmoothCurvesOfGenus B hZ g).val.obj) :
    ((integerComparison B hZ g hg).obj X).obj =
      (curvesSmallEquivalenceOver B hZ).hom.functor.obj X.obj := rfl

theorem integerComparison_map (g : ℕ) (hg : 2 ≤ g)
    {X Y : (moduliSmoothCurvesOfGenus B hZ g).val.obj} (a : X ⟶ Y) :
    ((integerComparison B hZ g hg).map a).hom =
      (curvesSmallEquivalenceOver B hZ).hom.functor.map a.hom := rfl

/-- Postcompose ANY actual original genus classifier with the derived
chosen-source functor; cartesianity is derived from the true source CFG. -/
def integerLift (T : BigFppfOver B integerBase hZ) (g : ℕ) (hg : 2 ≤ g)
    (F : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p T) :
    Functor.FiberedMor
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p T := by
  let H := integerComparison B hZ g hg
  have hH : H.toFunctor ⋙
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p =
      (moduliSmoothCurvesOfGenus B hZ g).val.p := H.w
  have hF : F.toFunctor ⋙ (moduliSmoothCurvesOfGenus B hZ g).val.p =
      Over.forget T := F.w
  have hw : (F.toFunctor ⋙ H.toFunctor) ⋙
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p =
      Over.forget T := by rw [Functor.assoc, hH, hF]
  refine { toFunctor := F.toFunctor ⋙ H.toFunctor, w := hw, cartesian := ?_ }
  intro x y a
  have : (Over.forget T).IsHomLift a.left a :=
    IsHomLift.of_fac' (Over.forget T) a.left a rfl rfl (by simp)
  have :
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p.IsHomLift
        a.left ((F.toFunctor ⋙ H.toFunctor).map a) :=
    Functor.isHomLift_map_of_comp_eq hw a.left a
  exact (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.property.isStronglyCartesian_homLift _ _

/-- In particular this is the SAME actual schematic classifier from the
proved native smooth-genus constructor. -/
def integerClassifier {Z T : BigFppfOver B integerBase hZ}
    (q : Z ⟶ T) (g : ℕ) (hg : 2 ≤ g)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    Functor.FiberedMor
      (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg).val.val.p T :=
  integerLift B hZ T g hg (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq)

variable (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

/-- The exact coefficient arrow used by the actual coarse-source constructor. -/
abbrev coefficientArrow := (integerSiteObject B hZ hK).hom

/-- Lift the specified TRUE original genus classifier to the exact chosen
native field stack. This includes the actual universal LG classifier. -/
def liftOriginalClassifier (T : BigFppfOver B (Spec (.of K)) hK)
    (g : ℕ) (hg : 2 ≤ g)
    (F : Functor.FiberedMor (moduliSmoothCurvesOfGenus B hZ g).val.p
      ((Over.map (coefficientArrow B hZ K hK)).obj T)) :
    BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val :=
  StackChangeOfBaseClassifier.lift B (Spec (.of K)) integerBase hK hZ
    (coefficientArrow B hZ K hK)
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg) T
    (integerLift B hZ ((Over.map (coefficientArrow B hZ K hK)).obj T) g hg F)

/-- The actual schematic genus classifier in the EXACT chosen native
field stack. No assumed field-stack equivalence or compatibility occurs. -/
def classifyingMor (T : BigFppfOver B (Spec (.of K)) hK)
    {Z : BigFppfOver B integerBase hZ}
    (q : Z ⟶ (Over.map (coefficientArrow B hZ K hK)).obj T)
    (g : ℕ) (hg : 2 ≤ g)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val :=
  liftOriginalClassifier B hZ K hK T g hg
    (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq)

/-- Its actual native stack morphism has this literal classifier functor. -/
def stackMorphism (T : BigFppfOver B (Spec (.of K)) hK)
    {Z : BigFppfOver B integerBase hZ}
    (q : Z ⟶ (Over.map (coefficientArrow B hZ K hK)).obj T)
    (g : ℕ) (hg : 2 ≤ g)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) :
    Stack.schemeStack.{u, u + 1} B (Spec (.of K)) hK T ⟶
      M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg :=
  StackChangeOfBaseClassifier.stackMorphism B (Spec (.of K)) integerBase hK hZ
    (coefficientArrow B hZ K hK)
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg) T
    (integerClassifier B hZ q g hg hq)

/-- Project to the SAME original CurveFamily category, retaining its
possibly nonschematic total space. -/
abbrev originalProjection (g : ℕ) (hg : 2 ≤ g) :
    (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj ⥤
      CurveFamily B hZ :=
  StackChangeOfBaseClassifier.originalProjection B (Spec (.of K)) integerBase hK hZ
    (coefficientArrow B hZ K hK)
    (M9StacksIntegration.GenusNineCoarse.smoothStack B hZ g hg) ⋙
      (M9StacksIntegration.GenusNineCoarse.smoothOpen B hZ g hg).property.ι ⋙
      (curvesSmallEquivalenceOver B hZ).inv.functor

/-- Recovery is the actual original hom-shrink unit, on EVERY slice
object, so later precomposition needs no classifier comparison premise. -/
def originalValueIso (T : BigFppfOver B (Spec (.of K)) hK)
    {Z : BigFppfOver B integerBase hZ}
    (q : Z ⟶ (Over.map (coefficientArrow B hZ K hK)).obj T)
    (g : ℕ) (hg : 2 ≤ g)
    (hq : M9StandaloneDraft.SchemeCurve
      ((BigFppfOver.toScheme B integerBase hZ).map q) g) (x : Over T) :
    (originalProjection B hZ K hK g hg).obj
        ((classifyingMor B hZ K hK T q g hg hq).obj x) ≅
      ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.obj
        ((Over.post (Over.map (coefficientArrow B hZ K hK))).obj x)).obj :=
  ((curvesSmallEquivalenceOver B hZ).unitIso.app
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q g hq).toFunctor.obj
      ((Over.post (Over.map (coefficientArrow B hZ K hK))).obj x)).obj).symm

/-- The projection preserves the specified original base and coefficient map. -/
theorem originalProjection_comp (g : ℕ) (hg : 2 ≤ g) :
    originalProjection B hZ K hK g hg ⋙ curvesProjectionOver B hZ =
      (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.p ⋙
        Over.map (coefficientArrow B hZ K hK) := by
  have hi : (curvesSmallEquivalenceOver B hZ).inv.functor ⋙ curvesProjectionOver B hZ =
      (curvesSmallBased B hZ).p := (curvesSmallEquivalenceOver B hZ).inv.w
  change (_ ⋙ _ ⋙ _) ⋙ _ = _
  rw [Functor.assoc, Functor.assoc, hi]
  exact StrictPullback.pr_comp_eq _ _

/-- ANY actual identity-base arrow in the chosen field stack gives an
identity-base arrow of the same original native curve families. -/
theorem original_isHomLift_id (g : ℕ) (hg : 2 ≤ g)
    {x y : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack B hZ K hK g hg).val.val.obj}
    (T : BigFppfOver B (Spec (.of K)) hK) (a : x ⟶ y)
    (ha : (M9StacksIntegration.GenusNineCoarseOverField.smoothStack
      B hZ K hK g hg).val.val.p.IsHomLift (𝟙 T) a) :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((Over.map (coefficientArrow B hZ K hK)).obj T))
      ((originalProjection B hZ K hK g hg).map a) := by
  have h := Functor.isHomLift_id_comp_functor
    (Over.map (coefficientArrow B hZ K hK)) ha
  rw [← originalProjection_comp B hZ K hK g hg] at h
  exact (Functor.isHomLift_comp_iff
    (originalProjection B hZ K hK g hg) (curvesProjectionOver B hZ) _ a).mp h

end M9Native.NativeSmoothGenusCoarseClassifier
