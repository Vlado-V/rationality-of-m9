module

public import M9StacksIntegration.LagrangianFieldBaseChange
public import M9StacksIntegration.LagrangianCoordinateFieldChange
public import M9StacksIntegration.LagrangianPrimitiveSectionsPullback

/-! Actual quotient, determinant-line, and all fourteen primitive-section
compatibilities for the genuine field-base-change morphism of LG. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Module
open AlgebraicGeometry.Grassmannian
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.LagrangianPullback M9Native.LagrangianMatrixChart
open M9Native.LagrangianPrimitiveSectionsPullback
open scoped BigOperators

universe u

namespace M9Native.LagrangianDeterminantFieldChange

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

theorem quotient_isomorphic :
    (pullbackPresentation (LagrangianFieldBaseChange.map φ) (quotientOnLG K)).Isomorphic
      (quotientOnLG L) := by
  apply presentation_isomorphic_of_class_eq
  calc
    _ = (⟦pullbackPresentation (LagrangianFieldBaseChange.map φ ≫ inclusion K)
      (universalQuotient K)⟧ : Points (space L) 3 6) :=
      (congrFun (pullbackPointsMap_comp (inclusion K) (LagrangianFieldBaseChange.map φ) 3 6)
        (⟦universalQuotient K⟧ : Points (grassmannian K) 3 6)).symm
    _ = ⟦pullbackPresentation (inclusion L ≫ LagrangianFieldBaseChange.grassMap φ)
      (universalQuotient K)⟧ := by rw [LagrangianFieldBaseChange.map_inclusion]
    _ = ⟦quotientOnLG L⟧ :=
      Quotient.sound (.rel _ _ (LagrangianFieldBaseChange.quotient_isomorphic φ (inclusion L)))

def quotientIso : (Scheme.Modules.pullback (LagrangianFieldBaseChange.map φ)).obj
    (quotientOnLG K).target ≅ (quotientOnLG L).target :=
  Classical.choose (quotient_isomorphic φ)

theorem quotientIso_triangle :
    (pullbackPresentation (LagrangianFieldBaseChange.map φ) (quotientOnLG K)).map ≫
      (quotientIso φ).hom = (quotientOnLG L).map := Classical.choose_spec (quotient_isomorphic φ)

def determinantIso : (Scheme.Modules.pullback (LagrangianFieldBaseChange.map φ)).obj
    (determinantLine K) ≅ determinantLine L :=
  exteriorPullbackIso (LagrangianFieldBaseChange.map φ) (quotientOnLG K).target 3 ≪≫
    (Scheme.Modules.exteriorPowerFunctor (space L) 3).mapIso (quotientIso φ)

theorem coefficientMap_map :
    LagrangianPlucker.coefficientMap K (LagrangianFieldBaseChange.map φ) =
      (LagrangianPlucker.coefficientMap L (𝟙 _)).comp φ := by
  ext a
  change (LagrangianFieldBaseChange.map φ ≫ projection K).appTop
      ((Scheme.ΓSpecIso (.of K)).inv a) =
    (projection L).appTop ((Scheme.ΓSpecIso (.of L)).inv (φ a))
  rw [LagrangianFieldBaseChange.map_projection]
  change (projection L).appTop
      ((GrassmannianFieldBaseChange.specMap φ).appTop ((Scheme.ΓSpecIso (.of K)).inv a)) = _
  congr 1
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

theorem primitiveSection_change_field (X : Scheme.{u}) (κ : L →+* Γ(X, ⊤))
    {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (j : Fin 14) :
    primitiveSection X K (κ.comp φ) q j = primitiveSection X L κ q j := by
  unfold primitiveSection
  apply Finset.sum_congr rfl
  intro i _
  have h := congrFun (congrFun
    (LagrangianCoordinateFieldChange.projectionMatrix_map φ) j) i
  change φ (LagrangianField.projectionMatrix K j i) = LagrangianField.projectionMatrix L j i at h
  rw [RingHom.comp_apply, h]

/-- The true determinant-line transport retains every original primitive
section, with the actual structural coefficient-ring maps. -/
theorem determinantIso_primitive (j : Fin 14) :
    (determinantIso φ).hom.app ⊤
      (pullbackGlobalSections (LagrangianFieldBaseChange.map φ) (determinantLine K)
        (primitiveSections K j)) = primitiveSections L j := by
  change (exteriorPowerMap (space L) (quotientIso φ).hom 3).app ⊤
    ((exteriorPullbackIso (LagrangianFieldBaseChange.map φ) (quotientOnLG K).target 3).hom.app ⊤
      (pullbackGlobalSections (LagrangianFieldBaseChange.map φ) (determinantLine K)
        (primitiveSections K j))) = _
  rw [primitiveSections_pullback, primitiveSection_postcomp, quotientIso_triangle,
    coefficientMap_map, primitiveSection_change_field]
  rfl

end M9Native.LagrangianDeterminantFieldChange
