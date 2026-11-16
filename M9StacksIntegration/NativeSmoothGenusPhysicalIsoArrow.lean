module

public import M9StacksIntegration.NativeSmoothGenusClassifierCurveIso

/-!
# Physical pullback isomorphisms give actual raw genus-classifier arrows

The genuine cartesian classifier comparisons identify both evaluated
families with the same native scheme pullbacks. An actual physical Scheme
isomorphism over their common original base gives a native total-space
isomorphism, its Yoneda isomorphism, and a full cartesian CurveFamily arrow.
Conjugation by the proved classifier comparisons returns the actual raw
classifier arrow over the identity. No raw arrow, natural isomorphism or
classifier-compatibility assertion is an input.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

namespace M9Native.NativeSmoothGenusPhysicalIsoArrow

open M9StacksIntegration.NativeSchematicCurveFamily
open NativeSmoothGenusClassifierCurveIso

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

def siteIso {A D : BigFppfOver B integerBase hZ}
    (e : (schemeFunctor B hZ).obj A ≅ (schemeFunctor B hZ).obj D) : A ≅ D := by
  let e₀ : A.left ≅ D.left :=
    { hom := ObjectProperty.homMk e.hom
      inv := ObjectProperty.homMk e.inv
      hom_inv_id := ObjectProperty.hom_ext _ e.hom_inv_id
      inv_hom_id := ObjectProperty.hom_ext _ e.inv_hom_id }
  exact Over.isoMk e₀
    (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

def rawFamilyIso {F G : CurveFamily B hZ}
    (β : F.base ≅ G.base) (ε : F.total ≅ G.total)
    (w : ε.hom ≫ G.toBase = F.toBase ≫ schemeSpaceMap β.hom) : F ≅ G where
  hom :=
    { baseMap := β.hom
      totalMap := ε.hom
      cartesian := by
        have : IsIso (schemeSpaceMap β.hom) :=
          (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso β).hom)
        exact IsPullback.of_horiz_isIso ⟨w⟩ }
  inv :=
    { baseMap := β.inv
      totalMap := ε.inv
      cartesian := by
        have : IsIso (schemeSpaceMap β.inv) :=
          (inferInstance : IsIso ((schemeSpaceFunctor B integerBase hZ).mapIso β).inv)
        refine IsPullback.of_horiz_isIso ⟨?_⟩
        rw [Iso.inv_comp_eq, ← Category.assoc, w, Category.assoc, ← schemeSpaceMap_comp,
          β.hom_inv_id, show schemeSpaceMap (𝟙 F.base) = 𝟙 _ from
            (schemeSpaceFunctor B integerBase hZ).map_id _, Category.comp_id] }
  hom_inv_id := CurveFamily.Hom.ext β.hom_inv_id ε.hom_inv_id
  inv_hom_id := CurveFamily.Hom.ext β.inv_hom_id ε.inv_hom_id

variable {Z₀ U₀ Z₁ U₁ T : BigFppfOver B integerBase hZ}
  (q₀ : Z₀ ⟶ U₀) (q₁ : Z₁ ⟶ U₁) (a₀ : T ⟶ U₀) (a₁ : T ⟶ U₁)
  (e : pullback ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀) ≅
    pullback ((schemeFunctor B hZ).map q₁) ((schemeFunctor B hZ).map a₁))
  (he : e.hom ≫ pullback.snd ((schemeFunctor B hZ).map q₁)
      ((schemeFunctor B hZ).map a₁) =
    pullback.snd ((schemeFunctor B hZ).map q₀) ((schemeFunctor B hZ).map a₀))

/-- The same physical isomorphism on the actual native pullback schemes. -/
def nativePhysicalIso : (schemeFunctor B hZ).obj (pullback q₀ a₀) ≅
    (schemeFunctor B hZ).obj (pullback q₁ a₁) :=
  physicalPullbackIso B hZ q₀ a₀ ≪≫ e ≪≫ (physicalPullbackIso B hZ q₁ a₁).symm

include he in
theorem nativePhysicalIso_hom_projection :
    (nativePhysicalIso B hZ q₀ q₁ a₀ a₁ e).hom ≫
      (schemeFunctor B hZ).map (pulledProjection B hZ q₁ a₁) =
    (schemeFunctor B hZ).map (pulledProjection B hZ q₀ a₀) := by
  have hi : (physicalPullbackIso B hZ q₁ a₁).inv ≫
      (schemeFunctor B hZ).map (pulledProjection B hZ q₁ a₁) =
      pullback.snd ((schemeFunctor B hZ).map q₁) ((schemeFunctor B hZ).map a₁) := by
    rw [Iso.inv_comp_eq, physicalPullbackIso_hom_snd]
  simp only [nativePhysicalIso, Iso.trans_hom, Iso.symm_hom, Category.assoc,
    hi, he, physicalPullbackIso_hom_snd]

/-- The original physical map is an actual arrow in the bounded native site. -/
def nativeTotalIso : pullback q₀ a₀ ≅ pullback q₁ a₁ :=
  siteIso B hZ (nativePhysicalIso B hZ q₀ q₁ a₀ a₁ e)

include he in
theorem nativeTotalIso_hom_projection :
    (nativeTotalIso B hZ q₀ q₁ a₀ a₁ e).hom ≫ pulledProjection B hZ q₁ a₁ =
      pulledProjection B hZ q₀ a₀ := by
  apply (schemeFunctor B hZ).map_injective
  rw [Functor.map_comp]
  exact nativePhysicalIso_hom_projection B hZ q₀ q₁ a₀ a₁ e he

/-- The actual native total-presheaf isomorphism is derived by Yoneda. -/
def nativeTotalPresheafIso : yoneda.obj (pullback q₀ a₀) ≅ yoneda.obj (pullback q₁ a₁) :=
  yoneda.mapIso (nativeTotalIso B hZ q₀ q₁ a₀ a₁ e)

/-- The actual represented total algebraic spaces are isomorphic. -/
def nativeTotalSpaceIso : schemeSpace (pullback q₀ a₀) ≅ schemeSpace (pullback q₁ a₁) :=
  (schemeSpaceFunctor B integerBase hZ).mapIso (nativeTotalIso B hZ q₀ q₁ a₀ a₁ e)

variable (g : ℕ)
  (hq₀ : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q₀) g)
  (hq₁ : M9StandaloneDraft.SchemeCurve ((schemeFunctor B hZ).map q₁) g)

/-- A genuine CurveFamily isomorphism of the same represented pullbacks,
with its full Cartesian square derived from the physical projection triangle. -/
def pulledFamilyIso : pulledFamily B hZ q₀ g hq₀ a₀ ≅ pulledFamily B hZ q₁ g hq₁ a₁ :=
  rawFamilyIso B hZ (Iso.refl T) (nativeTotalSpaceIso B hZ q₀ q₁ a₀ a₁ e) (by
    change schemeSpaceMap (nativeTotalIso B hZ q₀ q₁ a₀ a₁ e).hom ≫
      schemeSpaceMap (pulledProjection B hZ q₁ a₁) =
      schemeSpaceMap (pulledProjection B hZ q₀ a₀) ≫ schemeSpaceMap (𝟙 T)
    rw [show schemeSpaceMap (𝟙 T) = 𝟙 _ from
      (schemeSpaceFunctor B integerBase hZ).map_id T, Category.comp_id,
      ← schemeSpaceMap_comp, nativeTotalIso_hom_projection B hZ q₀ q₁ a₀ a₁ e he])

theorem pulledFamilyIso_hom_base :
    (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom.baseMap = 𝟙 T := rfl

theorem pulledFamilyIso_hom_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom := by
  have h := IsHomLift.map (curvesProjectionOver B hZ)
    (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom
  change (curvesProjectionOver B hZ).IsHomLift
    (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom.baseMap
    (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom at h
  rw [pulledFamilyIso_hom_base] at h
  exact h

/-- The actual raw evaluated genus-classifier values are isomorphic. -/
def classifierIso :
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₀ g hq₀).toFunctor.obj
      (Over.mk a₀)).obj ≅
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₁ g hq₁).toFunctor.obj
      (Over.mk a₁)).obj :=
  valueIso B hZ q₀ g hq₀ a₀ ≪≫
    pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁ ≪≫
    (valueIso B hZ q₁ g hq₁ a₁).symm

/-- The requested literal raw CurveFamily arrow; no arrow premise is supplied. -/
def classifierArrow :
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₀ g hq₀).toFunctor.obj
      (Over.mk a₀)).obj ⟶
    ((NativeSmoothGenusCurveClassifier.classifyingMor B hZ q₁ g hq₁).toFunctor.obj
      (Over.mk a₁)).obj :=
  (classifierIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom

/-- The raw arrow lies over the identity of the SAME original native test base. -/
theorem classifierArrow_lift :
    (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (classifierArrow B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁) := by
  have := valueIso_hom_lift B hZ q₀ g hq₀ a₀
  have := valueIso_hom_lift B hZ q₁ g hq₁ a₁
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      (valueIso B hZ q₁ g hq₁ a₁).inv := inferInstance
  have := pulledFamilyIso_hom_lift B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁
  have : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      ((pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom ≫
        (valueIso B hZ q₁ g hq₁ a₁).inv) :=
    IsHomLift.comp_lift_id_left _ (𝟙 T) _ _
  have h : (curvesProjectionOver B hZ).IsHomLift (𝟙 T)
      ((valueIso B hZ q₀ g hq₀ a₀).hom ≫
        (pulledFamilyIso B hZ q₀ q₁ a₀ a₁ e he g hq₀ hq₁).hom ≫
        (valueIso B hZ q₁ g hq₁ a₁).inv) :=
    IsHomLift.comp_lift_id_left _ (𝟙 T) _ _
  simpa only [classifierArrow, classifierIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc] using h

end M9Native.NativeSmoothGenusPhysicalIsoArrow
