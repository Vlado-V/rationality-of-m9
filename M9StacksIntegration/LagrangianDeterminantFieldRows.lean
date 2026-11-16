module

public import M9StacksIntegration.LagrangianDeterminantFieldChange
public import M9StacksIntegration.LineFramePullback

/-! Genuine pullback transport of arbitrary original determinant-section
row combinations across an actual field extension. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open M9Native.LagrangianGrassmannian M9Native.LagrangianPluckerQuotient
open M9Native.SectionZeroIdealFactorization
open scoped BigOperators

universe u

namespace M9Native.LagrangianDeterminantFieldRows

variable {K L : Type u} [Field K] [Field L] (φ : K →+* L)

def pullbackIso {T : Scheme.{u}} (f : T ⟶ space L) :
    (Scheme.Modules.pullback (f ≫ LagrangianFieldBaseChange.map φ)).obj (determinantLine K) ≅
      (Scheme.Modules.pullback f).obj (determinantLine L) :=
  ((Scheme.Modules.pullbackComp f (LagrangianFieldBaseChange.map φ)).app (determinantLine K)).symm ≪≫
    (Scheme.Modules.pullback f).mapIso (LagrangianDeterminantFieldChange.determinantIso φ)

theorem pullbackIso_primitive {T : Scheme.{u}} (f : T ⟶ space L) (i : Fin 14) :
    (pullbackIso φ f).hom.app ⊤
      (pullbackGlobalSections (f ≫ LagrangianFieldBaseChange.map φ) (determinantLine K)
        (primitiveSections K i)) = pullbackGlobalSections f (determinantLine L) (primitiveSections L i) := by
  change ((Scheme.Modules.pullback f).map (LagrangianDeterminantFieldChange.determinantIso φ).hom).app ⊤
    (((Scheme.Modules.pullbackComp f (LagrangianFieldBaseChange.map φ)).inv.app
      (determinantLine K)).app ⊤
      (pullbackGlobalSections (f ≫ LagrangianFieldBaseChange.map φ) (determinantLine K)
        (primitiveSections K i))) = _
  rw [LineFramePullback.pullbackComp_inv_apply, pullback_map_app_pullbackGlobalSections,
    LagrangianDeterminantFieldChange.determinantIso_primitive]

theorem row_zero_iff {T : Scheme.{u}} (f : T ⟶ space L) (c : Fin 14 → Γ(T, ⊤)) :
    (∑ i : Fin 14, c i • pullbackGlobalSections (f ≫ LagrangianFieldBaseChange.map φ)
      (determinantLine K) (primitiveSections K i)) = 0 ↔
    (∑ i : Fin 14, c i • pullbackGlobalSections f (determinantLine L) (primitiveSections L i)) = 0 := by
  have h : (pullbackIso φ f).hom.app ⊤
      (∑ i : Fin 14, c i • pullbackGlobalSections (f ≫ LagrangianFieldBaseChange.map φ)
        (determinantLine K) (primitiveSections K i)) =
      ∑ i : Fin 14, c i • pullbackGlobalSections f (determinantLine L) (primitiveSections L i) := by
    simp only [map_sum, Scheme.Modules.Hom.app_smul, pullbackIso_primitive]
  rw [← h]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((pullbackIso φ f).hom.app ⊤)).injective).symm

include φ in
theorem target_charZero [CharZero K] : CharZero L :=
  charZero_of_inj_zero fun n hn => by
    have h : (n : K) = 0 := φ.injective (by simpa using hn)
    exact Nat.cast_eq_zero.mp h

end M9Native.LagrangianDeterminantFieldRows
