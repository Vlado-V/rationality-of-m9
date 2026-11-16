module

public import M9StacksIntegration.FiniteFreeBasisPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeProjection

/-! # Genuine coordinate splittings of the original free rank-two sheaf -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u
namespace M9Native.FreeTwoCoordinates
open M9Native.LagrangianMatrixChart

/-- The other original coordinate of a rank-two free sheaf. -/
def other : Fin 2 → Fin 2 := ![1,0]

@[simp] theorem other_other (i : Fin 2) : other (other i) = i := by fin_cases i <;> rfl
@[simp] theorem other_ne_self (i : Fin 2) : other i ≠ i := by fin_cases i <;> decide

variable (X : Scheme.{u})

def inclusion (i : Fin 2) : Scheme.unitModule X ⟶ freeOn X 2 :=
  SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} i)

def projection (i : Fin 2) : freeOn X 2 ⟶ Scheme.unitModule X :=
  SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up.{u} i)

@[reassoc] theorem inclusion_projection (i j : Fin 2) :
    inclusion X i ≫ projection X j = if i=j then 𝟙 _ else 0 := by
  change SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} i) ≫
      SheafOfModules.freeProjection (R := X.ringCatSheaf) (ULift.up.{u} j) =
        if i=j then 𝟙 (SheafOfModules.unit X.ringCatSheaf) else 0
  simpa only [ULift.up.injEq] using
    SheafOfModules.ιFree_comp_freeProjection (R := X.ringCatSheaf)
      (ULift.up.{u} j) (ULift.up.{u} i)

@[reassoc (attr := simp)] theorem inclusion_projection_self (i : Fin 2) :
    inclusion X i ≫ projection X i = 𝟙 _ := by
  rw [inclusion_projection,ite_eq_left rfl]

@[reassoc (attr := simp)] theorem inclusion_projection_other (i : Fin 2) :
    inclusion X i ≫ projection X (other i) = 0 := by
  rw [inclusion_projection,ite_eq_right (Ne.symm (other_ne_self i))]

/-- The two actual projection-inclusion pairs sum to the identity. -/
theorem splitting_identity (i : Fin 2) :
    projection X i ≫ inclusion X i + projection X (other i) ≫ inclusion X (other i) =
      𝟙 (freeOn X 2) := by
  refine Cofan.IsColimit.hom_ext
    (SheafOfModules.isColimitFreeCofan (R := X.ringCatSheaf) (ULift.{u} (Fin 2))) _ _ (fun j => ?_)
  change inclusion X j.down ≫
    (projection X i ≫ inclusion X i + projection X (other i) ≫ inclusion X (other i)) =
      inclusion X j.down ≫ 𝟙 _
  rcases j with ⟨j⟩
  fin_cases i <;> fin_cases j <;>
    simp [other,Preadditive.comp_add,← Category.assoc,inclusion_projection]

/-- The actual coordinate projection has the original Kronecker basis values. -/
theorem projection_basis (i j : Fin 2) :
    (projection X i).app ⊤ (freeBasisSection X 2 j) =
      if j=i then (1 : Γ(X,⊤)) else (0 : Γ(X,⊤)) := by
  change Scheme.Modules.Hom.app (inclusion X j ≫ projection X i) ⊤ (1 : Γ(X,⊤)) = _
  rw [inclusion_projection]
  split_ifs <;> simp

/-- The original free one-coordinate sheaf is the actual unit module. -/
def singleBasis : freeOn X 1 ≅ Scheme.unitModule X :=
  coproductUniqueIso (fun _ : ULift.{u} (Fin 1) => SheafOfModules.unit X.ringCatSheaf)

@[reassoc (attr := simp)] theorem inclusion_singleBasis (j : ULift.{u} (Fin 1)) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) j ≫ (singleBasis X).hom = 𝟙 _ := by
  simp [singleBasis,SheafOfModules.ιFree]

/-- The actual unique basis section maps to one. -/
theorem singleBasis_basis :
    (singleBasis X).hom.app ⊤ (freeBasisSection X 1 0) = (1 : Γ(X,⊤)) := by
  change Scheme.Modules.Hom.app
    (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} (0 : Fin 1)) ≫
      (singleBasis X).hom) ⊤ (1 : Γ(X,⊤)) = _
  rw [inclusion_singleBasis]
  rfl

end M9Native.FreeTwoCoordinates
