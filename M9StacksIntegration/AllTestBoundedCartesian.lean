module

public import M9StacksIntegration.AllTestBoundedRestriction
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Cartesian original charts on the genuine bounded site

Restriction preserves the actual pullback square. Representable objects are
identified by the fully faithful bounded inclusion, and the two horizontal
chart maps use the explicit comparison isomorphisms. All morphisms remain
maps over the original coefficient field.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.AllTestBoundedCartesian
open AllTestBoundedCharts AllTestBoundedRestriction
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- Restriction to the actual bounded test category preserves cartesian
squares, by their pointwise universal property. -/
theorem restrict_isPullback {F₁ F₂ F₃ F₄ : M9StandaloneDraft.Presheaves K}
    {a : F₁ ⟶ F₂} {b : F₁ ⟶ F₃} {c : F₂ ⟶ F₄} {d : F₃ ⟶ F₄}
    (h : IsPullback a b c d) :
    IsPullback (restrictMap K B hK a) (restrictMap K B hK b)
      (restrictMap K B hK c) (restrictMap K B hK d) :=
  IsPullback.of_forall_isPullback_app fun U => h.app ((boundedInclusion B K hK).op.obj U)

/-- The actual representable comparison is natural in original scheme maps. -/
theorem restrictRepresentableIso_naturality
    {U T : BigFppfOver B (Spec (.of K)) hK} (v : U ⟶ T) :
    restrictMap K B hK (yoneda.map ((boundedInclusion B K hK).map v)) ≫
        (restrictRepresentableIso B K hK T).hom =
      (restrictRepresentableIso B K hK U).hom ≫ yoneda.map v := by
  ext V f
  rfl

/-- The restricted chart, with its domain the literal bounded representable. -/
def chartMap {F : M9StandaloneDraft.Presheaves K}
    (Z : BigFppfOver B (Spec (.of K)) hK)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F) :
    yoneda.obj Z ⟶ restrict K B hK F :=
  (restrictRepresentableIso B K hK Z).inv ≫ restrictMap K B hK r

/-- The restricted projection, with its target the literal bounded representable. -/
def baseMap {F : M9StandaloneDraft.Presheaves K}
    (T : BigFppfOver B (Spec (.of K)) hK)
    (π : F ⟶ yoneda.obj ((boundedInclusion B K hK).obj T)) :
    restrict K B hK F ⟶ yoneda.obj T :=
  restrictMap K B hK π ≫ (restrictRepresentableIso B K hK T).hom

/-- An actual original schematic chart square becomes the actual bounded
Yoneda chart square, without an assumed comparison of family categories. -/
theorem chart_isPullback {F : M9StandaloneDraft.Presheaves K}
    {Z U T : BigFppfOver B (Spec (.of K)) hK} (q : Z ⟶ U) (v : U ⟶ T)
    (r : yoneda.obj ((boundedInclusion B K hK).obj Z) ⟶ F)
    (π : F ⟶ yoneda.obj ((boundedInclusion B K hK).obj T))
    (h : IsPullback r (yoneda.map ((boundedInclusion B K hK).map q)) π
      (yoneda.map ((boundedInclusion B K hK).map v))) :
    IsPullback (chartMap K B hK Z r) (yoneda.map q) (baseMap K B hK T π)
      (yoneda.map v) := by
  apply (restrict_isPullback K B hK h).of_iso
    (restrictRepresentableIso B K hK Z) (Iso.refl _)
    (restrictRepresentableIso B K hK U) (restrictRepresentableIso B K hK T)
  · simp only [Iso.refl_hom, Category.comp_id, chartMap, Iso.hom_inv_id_assoc]
  · exact restrictRepresentableIso_naturality K B hK q
  · simp only [Iso.refl_hom, baseMap, Category.id_comp]
  · exact restrictRepresentableIso_naturality K B hK v

end M9StacksIntegration.AllTestBoundedCartesian
