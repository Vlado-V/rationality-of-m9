module

public import M9StacksIntegration.CoverFamilyStackPullback
public import M9StacksIntegration.FiniteDiagonalSchemePullbackBounds
public import M9StacksIntegration.NativeSmoothGenusCoarseClassifier
public import M9StacksIntegration.NativeSmoothGenusClassifierCurveIso
public import M9StacksIntegration.CurveClassifierPullback

/-!
# The original cover-family arrow on the actual M9 fibre product

The source classifier is the literal checked native genus-nine classifier
of the original schematic family. Its actual pullback is recovered by the
proved cartesian classifier-value comparison. Projecting the actual
universal comparison and then the original atlas projection constructs the
curve-family arrow. No family arrow, source classifier identity, algebraicity
or finite diagonal is supplied as an extra premise.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u

namespace M9Native.NativeCoverFamilyAtlasArrow

open NativeSmoothGenusCoarseClassifier

private theorem map_comp_eq_of_lift {C : Type*} [Category C]
    {E : Type*} [Category E] (p : E ⥤ C) {x y : E} {U V : C}
    (f : U ⟶ V) (a : x ⟶ y) (hx : p.obj x = U) (hy : p.obj y = V)
    [p.IsHomLift f a] : p.map a ≫ eqToHom hy = eqToHom hx ≫ f := by
  rw [IsHomLift.fac' p f a]
  simp

private theorem contains_of_proper (B : BigFppfSite.{u})
    {X T : Scheme.{u}} (hT : B.Contains T) (p : X ⟶ T) (hp : IsProper p) :
    B.Contains X := by
  have hqc : QuasiCompact p :=
    ⟨fun _ _ hc =>
      (@Scheme.Hom.isProperMap X T p hp.toUniversallyClosed).isCompact_preimage hc⟩
  exact @Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact B.cutoff X T p
    hp.toLocallyOfFiniteType hqc hT

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))

abbrev schemeFunctor := BigFppfOver.toScheme B integerBase hZ
abbrev integerBaseFunctor := Over.map (coefficientArrow B hZ K hK)
abbrev projection := originalProjection B hZ K hK 9 (by decide)

variable (Y V : BigFppfOver B (Spec (.of K)) hK)
  {Z : BigFppfOver B integerBase hZ}
  (q : Z ⟶ (integerBaseFunctor B hZ K hK).obj Y)
  (hq : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q) 9)

/-- The actual native genus-nine classifier of the original cover family. -/
abbrev sourceClassifier := stackMorphism B hZ K hK Y q 9 (by decide) hq

variable (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)

/-- The original curve family at the actual target-atlas identity point. -/
abbrev targetFamily : CurveFamily B hZ :=
  (projection B hZ K hK).obj (b.hom.hom.toFunctor.obj (Functor.FiberedMor.unit V))

/-- Its base is derived from the native projection square. -/
theorem targetFamily_base :
    (targetFamily B hZ K hK V b).base = (integerBaseFunctor B hZ K hK).obj V := by
  have h₁ := Functor.congr_obj (originalProjection_comp B hZ K hK 9 (by decide))
    (b.hom.hom.toFunctor.obj (Functor.FiberedMor.unit V))
  have h₂ := Functor.congr_obj b.hom.hom.w (Functor.FiberedMor.unit V)
  exact h₁.trans (congrArg (integerBaseFunctor B hZ K hK).obj h₂)

/-- The actual ground-field structure of this original target family. -/
def targetStructure :
    B.inclusion.obj (targetFamily B hZ K hK V b).base.left ⟶ Spec (.of K) :=
  eqToHom (congrArg (fun T : BigFppfOver B integerBase hZ => B.inclusion.obj T.left)
    (targetFamily_base B hZ K hK V b)) ≫ B.inclusion.map V.hom

variable {P : BigFppfOver B (Spec (.of K)) hK}
  (D : CoverFamilyStackPullback.PointData B hZ K hK Y V
    (sourceClassifier B hZ K hK Y q hq) b (P := P))

abbrev integerPoint := (integerBaseFunctor B hZ K hK).map D.left
abbrev pulledSite := pullback q (integerPoint B hZ K hK Y V q hq b D)
abbrev pulledProjectionNative :=
  NativeSmoothGenusClassifierCurveIso.pulledProjection B hZ q
    (integerPoint B hZ K hK Y V q hq b D)

/-- The real original scheme projection of the actual cover pullback. -/
abbrev pulledProjection :=
  (schemeFunctor B hZ).map (pulledProjectionNative B hZ K hK Y V q hq b D)

local instance pulledProper : IsProper (pulledProjection B hZ K hK Y V q hq b D) :=
  NativeSmoothGenusClassifierCurveIso.pulled_proper B hZ q 9 hq
    (integerPoint B hZ K hK Y V q hq b D)

local instance pulledSmooth :
    SmoothOfRelativeDimension 1 (pulledProjection B hZ K hK Y V q hq b D) :=
  NativeSmoothGenusClassifierCurveIso.pulled_smooth B hZ q 9 hq
    (integerPoint B hZ K hK Y V q hq b D)

abbrev pulledNativeFamily := NativeSmoothGenusClassifierCurveIso.pulledFamily B hZ
  q 9 hq (integerPoint B hZ K hK Y V q hq b D)

/-- The actual native classifier value is the very same schematic pullback. -/
def sourceValueIso :
    (projection B hZ K hK).obj
        ((sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj (Over.mk D.left)) ≅
      pulledNativeFamily B hZ K hK Y V q hq b D :=
  originalValueIso B hZ K hK Y q 9 (by decide) hq (Over.mk D.left) ≪≫
    NativeSmoothGenusClassifierCurveIso.valueIso B hZ q 9 hq
      (integerPoint B hZ K hK Y V q hq b D)

theorem sourceValueIso_hom_lift :
    (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((integerBaseFunctor B hZ K hK).obj P))
      (sourceValueIso B hZ K hK Y V q hq b D).hom := by
  let raw := ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).toFunctor.obj
    ((Over.post (integerBaseFunctor B hZ K hK)).obj (Over.mk D.left))).obj
  have hr : raw.base = (integerBaseFunctor B hZ K hK).obj P :=
    Functor.congr_obj (NativeSmoothGenusCurveClassifier.classifyingMor B hZ q 9 hq).w
      ((Over.post (integerBaseFunctor B hZ K hK)).obj (Over.mk D.left))
  have h₁ := (curvesSmallEquivalenceOver B hZ).isHomLift_unitIso_inv_app raw
  change (curvesProjectionOver B hZ).IsHomLift (𝟙 raw.base)
    (originalValueIso B hZ K hK Y q 9 (by decide) hq (Over.mk D.left)).hom at h₁
  rw [hr] at h₁
  haveI := h₁
  haveI := NativeSmoothGenusClassifierCurveIso.valueIso_hom_lift B hZ q 9 hq
    (integerPoint B hZ K hK Y V q hq b D)
  exact IsHomLift.comp_lift_id_left _ (𝟙 ((integerBaseFunctor B hZ K hK).obj P)) _ _

/-- The original target-classifier arrow from the pulled point to its
identity value, preceded by the actual universal M9 comparison. -/
def targetStep :
    (sourceClassifier B hZ K hK Y q hq).hom.hom.toFunctor.obj (Over.mk D.left) ⟶
      b.hom.hom.toFunctor.obj (Functor.FiberedMor.unit V) :=
  D.comparison.hom ≫ b.hom.hom.toFunctor.map (Over.homMk D.right (by simp))

theorem targetStep_lift :
    (CoverFamilyStackPullback.sourceStack B hZ K hK).val.val.p.IsHomLift D.right
      (targetStep B hZ K hK Y V q hq b D) := by
  haveI := D.vertical
  let ρ : Over.mk D.right ⟶ Functor.FiberedMor.unit V := Over.homMk D.right (by simp)
  haveI : (Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V).val.val.p.IsHomLift
      D.right ρ := by
    change (Over.forget V).IsHomLift D.right ρ
    exact IsHomLift.of_fac' (Over.forget V) D.right ρ rfl rfl rfl
  haveI := Functor.isHomLift_map_of_comp_eq b.hom.hom.w D.right ρ
  exact IsHomLift.comp_lift_id_left _ D.right _ _

/-- The genuine original curve-family arrow into the actual atlas family. -/
def nativeFamilyArrow : pulledNativeFamily B hZ K hK Y V q hq b D ⟶
    targetFamily B hZ K hK V b :=
  (sourceValueIso B hZ K hK Y V q hq b D).inv ≫
    (projection B hZ K hK).map (targetStep B hZ K hK Y V q hq b D)

theorem nativeFamilyArrow_lift :
    (curvesProjectionOver B hZ).IsHomLift
      ((integerBaseFunctor B hZ K hK).map D.right)
      (nativeFamilyArrow B hZ K hK Y V q hq b D) := by
  have hγ := Functor.isHomLift_comp_functor (integerBaseFunctor B hZ K hK) D.right
    (targetStep B hZ K hK Y V q hq b D)
    (targetStep_lift B hZ K hK Y V q hq b D)
  rw [← originalProjection_comp B hZ K hK 9 (by decide)] at hγ
  haveI := (Functor.isHomLift_comp_iff (projection B hZ K hK)
    (curvesProjectionOver B hZ) ((integerBaseFunctor B hZ K hK).map D.right)
    (targetStep B hZ K hK Y V q hq b D)).mp hγ
  haveI := sourceValueIso_hom_lift B hZ K hK Y V q hq b D
  haveI : (curvesProjectionOver B hZ).IsHomLift
      (𝟙 ((integerBaseFunctor B hZ K hK).obj P))
      (sourceValueIso B hZ K hK Y V q hq b D).inv := inferInstance
  exact IsHomLift.comp_lift_id_left _ ((integerBaseFunctor B hZ K hK).map D.right) _ _

/-- The native family arrow retains the SAME original map to the target
atlas, with only the derived equality of its integer base. -/
theorem nativeFamilyArrow_base :
    (nativeFamilyArrow B hZ K hK Y V q hq b D).baseMap ≫
        eqToHom (targetFamily_base B hZ K hK V b) =
      (integerBaseFunctor B hZ K hK).map D.right := by
  have := nativeFamilyArrow_lift B hZ K hK Y V q hq b D
  exact map_comp_eq_of_lift (curvesProjectionOver B hZ)
    ((integerBaseFunctor B hZ K hK).map D.right)
    (nativeFamilyArrow B hZ K hK Y V q hq b D) rfl
    (targetFamily_base B hZ K hK V b)

theorem nativeFamilyArrow_ground :
    B.inclusion.map (nativeFamilyArrow B hZ K hK Y V q hq b D).baseMap.left ≫
        targetStructure B hZ K hK V b = B.inclusion.map P.hom := by
  have hb := congrArg (fun f => B.inclusion.map f.left)
    (nativeFamilyArrow_base B hZ K hK Y V q hq b D)
  simp only [Over.comp_left, Over.eqToHom_left, Functor.map_comp, eqToHom_map] at hb
  dsimp only [targetStructure]
  rw [← Category.assoc, hb]
  change B.inclusion.map D.right.left ≫ B.inclusion.map V.hom = _
  rw [← Functor.map_comp, Over.w]

/-- The identity scheme map to the same original integer-site object. -/
def originalBaseMap (T : BigFppfOver B integerBase hZ) :
    integerSiteObject B hZ T.left.property ⟶ T :=
  Over.homMk (ObjectProperty.homMk (𝟙 _)) (by
    apply B.inclusion.map_injective
    exact specULiftZIsTerminal.hom_ext _ _)

/-- An actual physical pullback isomorphism gives its real original
cartesian curve-family arrow. This generic helper is used with the derived
native pullback isomorphism below. -/
def originalToNative {A T : BigFppfOver B integerBase hZ} (r : A ⟶ T)
    [IsProper ((schemeFunctor B hZ).map r)]
    [SmoothOfRelativeDimension 1 ((schemeFunctor B hZ).map r)]
    {X : Scheme.{u}} (hX : B.Contains X) (p : X ⟶ (schemeFunctor B hZ).obj T)
    [IsProper p] [SmoothOfRelativeDimension 1 p]
    (ε : X ≅ (schemeFunctor B hZ).obj A)
    (hε : ε.hom ≫ (schemeFunctor B hZ).map r = p) :
    CurveClassifierPullback.originalFamily B hZ hX T.left.property p ⟶
      M9StacksIntegration.NativeSchematicCurveFamily.properSmoothSchemeFamily B hZ r
        inferInstance inferInstance :=
  NativeSchematicCurveCartesianArrow.arrow B hZ r
    (CurveClassifierPullback.siteMap B hZ hX T.left.property p)
    (originalBaseMap B hZ T)
    (Over.homMk (ObjectProperty.homMk ε.hom) (by
      apply B.inclusion.map_injective
      exact specULiftZIsTerminal.hom_ext _ _))
    inferInstance inferInstance
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : IsProper p))
    (by simpa only [CurveClassifierPullback.siteMap_toScheme] using
      (inferInstance : SmoothOfRelativeDimension 1 p))
    (by
      change IsPullback ε.hom p ((schemeFunctor B hZ).map r) (𝟙 _)
      exact IsPullback.of_horiz_isIso ⟨by simpa using hε⟩)

/-- The unchanged scheme-theoretic pullback of the original cover family. -/
abbrev physicalSourceScheme :=
  pullback ((schemeFunctor B hZ).map q) (B.inclusion.map D.left.left)

abbrev physicalSourceProjection : physicalSourceScheme B hZ K hK Y V q hq b D ⟶
    B.inclusion.obj P.left :=
  pullback.snd ((schemeFunctor B hZ).map q) (B.inclusion.map D.left.left)

local instance physicalSourceProper :
    IsProper (physicalSourceProjection B hZ K hK Y V q hq b D) := by
  have : IsProper ((schemeFunctor B hZ).map q) := hq.1
  exact inferInstanceAs
    (IsProper (pullback.snd ((schemeFunctor B hZ).map q) (B.inclusion.map D.left.left)))

local instance physicalSourceSmooth :
    SmoothOfRelativeDimension 1 (physicalSourceProjection B hZ K hK Y V q hq b D) := by
  have : SmoothOfRelativeDimension 1 ((schemeFunctor B hZ).map q) := hq.2.1
  exact inferInstanceAs
    (SmoothOfRelativeDimension 1
      (pullback.snd ((schemeFunctor B hZ).map q) (B.inclusion.map D.left.left)))

/-- Containment follows from the genuine proper projection to the actual P. -/
theorem physicalSource_contains : B.Contains (physicalSourceScheme B hZ K hK Y V q hq b D) := by
  let pP := physicalSourceProjection B hZ K hK Y V q hq b D
  have hp : IsProper pP := physicalSourceProper B hZ K hK Y V q hq b D
  exact contains_of_proper B P.left.property pP hp

/-- The literal original schematic family of this same real pullback. -/
abbrev originalSourceFamily :=
  @CurveClassifierPullback.originalFamily B hZ _ _
    (physicalSource_contains B hZ K hK Y V q hq b D) P.left.property
    (physicalSourceProjection B hZ K hK Y V q hq b D)
    (physicalSourceProper B hZ K hK Y V q hq b D)
    (physicalSourceSmooth B hZ K hK Y V q hq b D)

/-- The requested original family arrow is constructed from the genuine
pullback and the actual universal native comparison. -/
def familyArrow : originalSourceFamily B hZ K hK Y V q hq b D ⟶
    targetFamily B hZ K hK V b := by
  have : IsProper (physicalSourceProjection B hZ K hK Y V q hq b D) :=
    physicalSourceProper B hZ K hK Y V q hq b D
  have : SmoothOfRelativeDimension 1
      (physicalSourceProjection B hZ K hK Y V q hq b D) :=
    physicalSourceSmooth B hZ K hK Y V q hq b D
  have : IsProper (pulledProjection B hZ K hK Y V q hq b D) :=
    pulledProper B hZ K hK Y V q hq b D
  have : SmoothOfRelativeDimension 1 (pulledProjection B hZ K hK Y V q hq b D) :=
    pulledSmooth B hZ K hK Y V q hq b D
  exact originalToNative B hZ (pulledProjectionNative B hZ K hK Y V q hq b D)
    (physicalSource_contains B hZ K hK Y V q hq b D)
    (physicalSourceProjection B hZ K hK Y V q hq b D)
    (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso B hZ q
      (integerPoint B hZ K hK Y V q hq b D)).symm
    (by
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact (NativeSmoothGenusClassifierCurveIso.physicalPullbackIso_hom_snd B hZ q
        (integerPoint B hZ K hK Y V q hq b D)).symm) ≫
    nativeFamilyArrow B hZ K hK Y V q hq b D

/-- Its original ground square is the actual original P→V square. -/
theorem familyArrow_ground :
    B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left ≫
        targetStructure B hZ K hK V b = B.inclusion.map P.hom := by
  change (𝟙 _ ≫ B.inclusion.map
      (nativeFamilyArrow B hZ K hK Y V q hq b D).baseMap.left) ≫ _ = _
  simpa only [Category.id_comp] using
    nativeFamilyArrow_ground B hZ K hK Y V q hq b D

/-- The literal original family arrow has the SAME actual universal
parameter projection P→V, through the derived target-base isomorphism. -/
theorem familyArrow_base :
    B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left ≫
        eqToHom (congrArg (fun T : BigFppfOver B integerBase hZ => B.inclusion.obj T.left)
          (targetFamily_base B hZ K hK V b)) = B.inclusion.map D.right.left := by
  have hb := congrArg (fun f => B.inclusion.map f.left)
    (nativeFamilyArrow_base B hZ K hK Y V q hq b D)
  change (𝟙 _ ≫ B.inclusion.map
      (nativeFamilyArrow B hZ K hK Y V q hq b D).baseMap.left) ≫ _ = _
  simpa only [Category.id_comp, Over.comp_left, Over.eqToHom_left,
    Functor.map_comp, eqToHom_map, integerBaseFunctor, Over.map_map_left] using hb

/-- The original source scheme projection is genuinely a pullback of the
same original cover-family projection and the SAME original P→Y map. -/
theorem physicalPullback : IsPullback
    ((schemeFunctor B hZ).map
      (pullback.fst q (integerPoint B hZ K hK Y V q hq b D)))
    (pulledProjection B hZ K hK Y V q hq b D)
    ((schemeFunctor B hZ).map q) (B.inclusion.map D.left.left) :=
  NativeSmoothGenusClassifierCurveIso.physicalPullback B hZ q
    (integerPoint B hZ K hK Y V q hq b D)

/-- The real finite scheme pullback, its universal comparison and the
original grounded family arrow are all conclusions of the actual source
constructor and its actual genus-nine family classifier. -/
theorem exists_scheme_and_originalFamilyArrow :
    ∃ (P : BigFppfOver B (Spec (.of K)) hK)
      (qP : P ⟶ FiniteDiagonalSchemePullback.productSite B (Spec (.of K)) hK Y V)
      (e : StacksRepresentableCFG.EquivalenceOver (Over.forget P)
        (CoverFamilyStackPullback.pairProjection B hZ K hK Y V
          (sourceClassifier B hZ K hK Y q hq) b))
      (D : CoverFamilyStackPullback.PointData B hZ K hK Y V
        (sourceClassifier B hZ K hK Y q hq) b (P := P)),
      IsFinite ((BigFppfOver.toScheme B (Spec (.of K)) hK).map qP) ∧
      e.hom.functor.obj (Over.mk (𝟙 P)) =
        CoverFamilyStackPullback.pointObject B hZ K hK Y V
          (sourceClassifier B hZ K hK Y q hq) b D ∧
      B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left ≫
        targetStructure B hZ K hK V b = B.inclusion.map P.hom := by
  obtain ⟨P, qP, hqP, ⟨e⟩⟩ := CoverFamilyStackPullback.exists_scheme B hZ K hK Y V
    (sourceClassifier B hZ K hK Y q hq) b
  obtain ⟨D, hD⟩ := CoverFamilyStackPullback.exists_pointData B hZ K hK Y V
    (sourceClassifier B hZ K hK Y q hq) b e
  exact ⟨P, qP, e, D, hqP, hD, familyArrow_ground B hZ K hK Y V q hq b D⟩

/-- With the original finite-type quasi-compact source and target bases,
the SAME actual representing scheme has both required ground bounds. -/
theorem exists_finiteType_scheme_and_originalFamilyArrow
    [QuasiCompact (B.inclusion.map Y.hom)]
    [LocallyOfFiniteType (B.inclusion.map Y.hom)]
    [QuasiCompact (B.inclusion.map V.hom)]
    [LocallyOfFiniteType (B.inclusion.map V.hom)] :
    ∃ (P : BigFppfOver B (Spec (.of K)) hK)
      (qP : P ⟶ FiniteDiagonalSchemePullback.productSite B (Spec (.of K)) hK Y V)
      (e : StacksRepresentableCFG.EquivalenceOver (Over.forget P)
        (CoverFamilyStackPullback.pairProjection B hZ K hK Y V
          (sourceClassifier B hZ K hK Y q hq) b))
      (D : CoverFamilyStackPullback.PointData B hZ K hK Y V
        (sourceClassifier B hZ K hK Y q hq) b (P := P)),
      IsFinite ((BigFppfOver.toScheme B (Spec (.of K)) hK).map qP) ∧
      QuasiCompact (B.inclusion.map P.hom) ∧
      LocallyOfFiniteType (B.inclusion.map P.hom) ∧
      e.hom.functor.obj (Over.mk (𝟙 P)) =
        CoverFamilyStackPullback.pointObject B hZ K hK Y V
          (sourceClassifier B hZ K hK Y q hq) b D ∧
      B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left ≫
        targetStructure B hZ K hK V b = B.inclusion.map P.hom ∧
      QuasiCompact (B.inclusion.map D.right.left) ∧
      LocallyOfFiniteType (B.inclusion.map D.right.left) ∧
      QuasiCompact (B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left) ∧
      LocallyOfFiniteType
        (B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left) := by
  obtain ⟨P, qP, e, D, hqP, hD, hβ⟩ :=
    exists_scheme_and_originalFamilyArrow B hZ K hK Y V q hq b
  obtain ⟨hqc, hft⟩ :=
    FiniteDiagonalSchemePullbackBounds.finite_over_product_structural_properties
      B (Spec (.of K)) hK Y V P qP hqP
  have := hqc
  have := hft
  have hv : B.inclusion.map D.right.left ≫ B.inclusion.map V.hom =
      B.inclusion.map P.hom := by rw [← Functor.map_comp, Over.w]
  obtain ⟨hvqc, hvft⟩ := FiniteDiagonalSchemePullbackBounds.overField_morphism_properties
    K (B.inclusion.map P.hom) (B.inclusion.map V.hom)
    (B.inclusion.map D.right.left) hv
  obtain ⟨hβqc, hβft⟩ := FiniteDiagonalSchemePullbackBounds.overField_morphism_properties
    K (B.inclusion.map P.hom) (targetStructure B hZ K hK V b)
    (B.inclusion.map (familyArrow B hZ K hK Y V q hq b D).baseMap.left) hβ
  exact ⟨P, qP, e, D, hqP, hqc, hft, hD, hβ, hvqc, hvft, hβqc, hβft⟩

end M9Native.NativeCoverFamilyAtlasArrow
