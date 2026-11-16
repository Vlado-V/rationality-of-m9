module

public import M9StacksIntegration.RankTwoSelectedPairSheafEntries
public import M9StacksIntegration.FreeTwoCoordinates
public import M9StacksIntegration.LagrangianSectionGeneration

/-! A genuine unit entry of a determinant-zero selected pair gives an
actual split image subline and the exact two original section values.
Both the target row and the selected source position are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
universe u v
namespace M9Native.RankTwoUnitPivotColumns
open LagrangianMatrixChart FreeTwoCoordinates Stacks.FreeSheafMatrix

section Ring
variable {R : Type v} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R)

theorem pivotMinor_eq_zero (hdet : M.det=0) (row col : Fin 2) :
    M row col * M (other row) (other col) -
      M row (other col) * M (other row) col = 0 := by
  have hr : row=0 ∨ row=1 := by omega
  have hc : col=0 ∨ col=1 := by omega
  rcases hr with rfl | rfl <;> rcases hc with rfl | rfl
  all_goals
    simp only [Matrix.det_fin_two] at hdet
    simp only [other, Matrix.cons_val_zero, Matrix.cons_val_one]
    first | exact hdet | linear_combination hdet | linear_combination -hdet

theorem other_column_eq (hdet : M.det=0) (row col : Fin 2)
    (a : Rˣ) (ha : M row col = (a : R)) (r : Fin 2) :
    M r (other col) = ((↑a⁻¹ : R) * M row (other col)) * M r col := by
  by_cases hr : r=row
  · subst r
    rw [ha]
    calc
      _ = (↑a⁻¹ : R) * (M row (other col) * (a : R)) := by
        rw [mul_comm (M row (other col)) (a : R), ← mul_assoc]
        simp
      _ = _ := by ring
  · have hr' : r=other row := by
      have hrow : row=0 ∨ row=1 := by omega
      rcases hrow with rfl | rfl <;> fin_cases r <;> simp_all [other]
    subst r
    have hm := pivotMinor_eq_zero M hdet row col
    rw [ha] at hm
    calc
      _ = (↑a⁻¹ : R) * ((a : R) * M (other row) (other col)) := by
        simp [← mul_assoc]
      _ = (↑a⁻¹ : R) * (M row (other col) * M (other row) col) := by
        rw [sub_eq_zero.mp hm]
      _ = _ := by ring
end Ring

variable (X : Scheme.{u}) {F : X.Modules} (eF : F ≅ freeOn X 2)
  (s : Fin 2 → Γ(F,⊤))

def sectionMatrix : Matrix (Fin 2) (Fin 2) Γ(X,⊤) :=
  fun row col => freeSectionCoordinates X 2 (eF.hom.app ⊤ (s col)) row

variable (row col : Fin 2) (a : Γ(X,⊤)ˣ)

def coefficient : Γ(X,⊤) := (↑a⁻¹ : Γ(X,⊤)) * sectionMatrix X eF s row (other col)

def subline : Scheme.unitModule X ⟶ F := Scheme.Modules.unitHomEquivTop F (s col)

def retraction : F ⟶ Scheme.unitModule X :=
  eF.hom ≫ FreeTwoCoordinates.projection X row ≫ scalarEnd (↑a⁻¹ : Γ(X,⊤))

def scalarMap : Scheme.unitModule X ⟶ Scheme.unitModule X :=
  scalarEnd (coefficient X eF s row col a)

theorem subline_one : (subline X s col).app ⊤ (1 : Γ(X,⊤)) = s col :=
  LagrangianAffineDeterminant.unitHom_top_one F (s col)

theorem subline_retraction
    (ha : sectionMatrix X eF s row col = (a : Γ(X,⊤))) :
    subline X s col ≫ retraction X eF row a = 𝟙 (Scheme.unitModule X) := by
  apply unitEndValue_injective
  change unitEndValue
    ((subline X s col ≫ eF.hom ≫ FreeTwoCoordinates.projection X row) ≫
      scalarEnd (↑a⁻¹ : Γ(X,⊤))) = 1
  rw [unitEndValue_comp, unitEndValue_scalarEnd]
  have hv : unitEndValue
      (subline X s col ≫ eF.hom ≫ FreeTwoCoordinates.projection X row) =
        sectionMatrix X eF s row col := by
    change (FreeTwoCoordinates.projection X row).app ⊤
      (eF.hom.app ⊤ ((subline X s col).app ⊤ (1 : Γ(X,⊤)))) = _
    rw [subline_one]
    change _ = freeSectionCoordinates X 2 (eF.hom.app ⊤ (s col)) row
    rw [freeSectionCoordinates_apply,freeProj_eq_freeProjection]
    rfl
  rw [hv,ha]
  simp

theorem other_section_eq
    (hdet : (sectionMatrix X eF s).det=0)
    (ha : sectionMatrix X eF s row col = (a : Γ(X,⊤))) :
    s (other col) = coefficient X eF s row col a • s col := by
  apply (ConcreteCategory.bijective_of_isIso (eF.hom.app ⊤)).injective
  apply (freeSectionCoordinates X 2).injective
  ext r
  rw [Scheme.Modules.Hom.app_smul, map_smul]
  exact other_column_eq (sectionMatrix X eF s) hdet row col a ha r

theorem original_pair_eq
    (hdet : (sectionMatrix X eF s).det=0)
    (ha : sectionMatrix X eF s row col = (a : Γ(X,⊤))) (k : Fin 2) :
    s k = if k=col then (subline X s col).app ⊤ (1 : Γ(X,⊤)) else
      (subline X s col).app ⊤ ((scalarMap X eF s row col a).app ⊤ (1 : Γ(X,⊤))) := by
  by_cases hk : k=col
  · subst k
    rw [ite_eq_left rfl,subline_one]
  · have hk' : k=other col := by
      have hc : col=0 ∨ col=1 := by omega
      rcases hc with rfl | rfl <;> fin_cases k <;> simp_all [other]
    rw [ite_eq_right hk,hk',other_section_eq X eF s row col a hdet ha]
    have hc : (scalarMap X eF s row col a).app ⊤ (1 : Γ(X,⊤)) =
        coefficient X eF s row col a := unitEndValue_scalarEnd _
    rw [hc,show coefficient X eF s row col a =
      coefficient X eF s row col a • (1 : Γ(X,⊤)) by simp,
      Scheme.Modules.Hom.app_smul,subline_one]
    simp only [smul_eq_mul,mul_one]

end M9Native.RankTwoUnitPivotColumns
