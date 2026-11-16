module

public import M9StacksIntegration.NativeSchematicCurveCartesianArrow
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# Actual identity-base curve-family arrows give physical scheme isomorphisms

The input is an actual native Cartesian family arrow between represented
proper smooth curve families. Its identity base makes the total map an
isomorphism. Native Yoneda then recovers an isomorphism of the SAME schemes,
with the literal projection triangle. Ordinary Scheme pullback allows any
original base, including field spectra outside the native site.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
namespace M9Native
namespace NativeSchematicCurveIdentityIso

open M9StacksIntegration.NativeSchematicCurveFamily

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  {Z₀ Z₁ T : BigFppfOver B integerBase hZ}
  (q₀ : Z₀ ⟶ T) (q₁ : Z₁ ⟶ T)
  (hp₀ : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q₀))
  (hs₀ : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q₀))
  (hp₁ : IsProper ((BigFppfOver.toScheme B integerBase hZ).map q₁))
  (hs₁ : SmoothOfRelativeDimension 1 ((BigFppfOver.toScheme B integerBase hZ).map q₁))
  (δ : properSmoothSchemeFamily B hZ q₀ hp₀ hs₀ ⟶
    properSmoothSchemeFamily B hZ q₁ hp₁ hs₁)
  (hδ : δ.baseMap = 𝟙 T)

include hδ

/-- The native total map is invertible by its actual Cartesian square,
not by a supplied total-space isomorphism. -/
theorem totalMap_isIso : IsIso δ.totalMap := by
  have : IsIso δ.baseMap := hδ.symm ▸ IsIso.id T
  have : IsIso (schemeSpaceMap δ.baseMap) :=
    Functor.map_isIso (schemeSpaceFunctor B integerBase hZ) δ.baseMap
  exact δ.cartesian.isIso_fst_of_isIso

/-- The actual native represented total map comes from a physical scheme
isomorphism over the identity of the given base. -/
theorem exists_physicalIso :
    ∃ e : (BigFppfOver.toScheme B integerBase hZ).obj Z₀ ≅
        (BigFppfOver.toScheme B integerBase hZ).obj Z₁,
      e.hom ≫ (BigFppfOver.toScheme B integerBase hZ).map q₁ =
        (BigFppfOver.toScheme B integerBase hZ).map q₀ := by
  have : IsIso δ.totalMap := totalMap_isIso B hZ q₀ q₁ hp₀ hs₀ hp₁ hs₁ δ hδ
  have : IsIso δ.totalMap.hom :=
    Functor.map_isIso (ObjectProperty.ι (IsAlgebraicSpace B integerBase hZ)) δ.totalMap
  let r : Z₀ ⟶ Z₁ := yoneda.preimage δ.totalMap.hom
  have hr : yoneda.map r = δ.totalMap.hom := yoneda.map_preimage _
  have : IsIso (yoneda.map r) := by rw [hr]; infer_instance
  have : IsIso r := Yoneda.fullyFaithful.isIso_of_isIso_map r
  have hq : r ≫ q₁ = q₀ := by
    apply yoneda.map_injective
    rw [Functor.map_comp, hr]
    have h := congrArg (fun m => m.hom) δ.cartesian.w
    change δ.totalMap.hom ≫ yoneda.map q₁ = yoneda.map q₀ ≫ yoneda.map δ.baseMap at h
    rw [hδ, (yoneda (C := BigFppfOver B integerBase hZ)).map_id, Category.comp_id] at h
    exact h
  refine ⟨(BigFppfOver.toScheme B integerBase hZ).mapIso (asIso r), ?_⟩
  change (BigFppfOver.toScheme B integerBase hZ).map r ≫ _ = _
  rw [← Functor.map_comp, hq]

def physicalIso : (BigFppfOver.toScheme B integerBase hZ).obj Z₀ ≅
    (BigFppfOver.toScheme B integerBase hZ).obj Z₁ :=
  (exists_physicalIso B hZ q₀ q₁ hp₀ hs₀ hp₁ hs₁ δ hδ).choose

theorem physicalIso_hom_snd :
    (physicalIso B hZ q₀ q₁ hp₀ hs₀ hp₁ hs₁ δ hδ).hom ≫
        (BigFppfOver.toScheme B integerBase hZ).map q₁ =
      (BigFppfOver.toScheme B integerBase hZ).map q₀ :=
  (exists_physicalIso B hZ q₀ q₁ hp₀ hs₀ hp₁ hs₁ δ hδ).choose_spec

end NativeSchematicCurveIdentityIso

namespace PhysicalCurveIsoPullback

variable {X₀ X₁ S W : Scheme.{u}} (q₀ : X₀ ⟶ S) (q₁ : X₁ ⟶ S)
  (e : X₀ ≅ X₁) (he : e.hom ≫ q₁ = q₀) (w : W ⟶ S)

/-- Pull back an actual physical scheme isomorphism over its literal
base. The new base is an arbitrary original scheme, with no site input. -/
def baseChangeIso : pullback q₀ w ≅ pullback q₁ w :=
  (Over.forget W).mapIso
    ((Over.pullback w).mapIso (Over.isoMk e he : Over.mk q₀ ≅ Over.mk q₁))

theorem baseChangeIso_hom_snd :
    (baseChangeIso q₀ q₁ e he w).hom ≫ pullback.snd q₁ w = pullback.snd q₀ w :=
  Over.w ((Over.pullback w).mapIso (Over.isoMk e he : Over.mk q₀ ≅ Over.mk q₁)).hom

end PhysicalCurveIsoPullback
end M9Native
