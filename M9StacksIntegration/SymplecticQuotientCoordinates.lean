module

public import M9StacksIntegration.SymplecticQuotientEvaluation
public import M9StacksIntegration.LagrangianLocalPairing

/-!
# Original open coordinates of the genuine symplectic dual embedding

The signs are computed from the actual J matrix, not supplied by a
normalization premise. All local coefficients are the frozen genuine
dual evaluations on the original six quotient sections.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance] _root_.Stacks.SchemeCohomology.sheafOfModules_abelian

namespace M9Native.SymplecticQuotientCoordinates

open LagrangianMatrixChart LagrangianDualCoefficients SymplecticQuotientEvaluation

theorem standardForm_first (R : Type u) [CommRing R] (i : Fin 3) (j : Fin 6) :
    LagrangianTransitivity.standardForm R (i.castAdd 3) j =
      -(if j = Fin.natAdd 3 i then 1 else 0) := by
  classical
  change Matrix.J (Fin 3) R (finSumFinEquiv.symm (i.castAdd 3))
    (finSumFinEquiv.symm j) = _
  rw [finSumFinEquiv_symm_apply_castAdd]
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · rw [finSumFinEquiv_symm_apply_castAdd]
    have h : j.castAdd 3 ≠ Fin.natAdd 3 i := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have h' : j.castAdd 3 ≠ i.addNat 3 := by
      simpa only [Fin.natAdd_eq_addNat] using h
    simp [Matrix.J, Matrix.fromBlocks, h']
  · rw [finSumFinEquiv_symm_apply_natAdd]
    simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Fin.ext_iff, eq_comm]

theorem standardForm_last (R : Type u) [CommRing R] (i : Fin 3) (j : Fin 6) :
    LagrangianTransitivity.standardForm R (Fin.natAdd 3 i) j =
      (if j = i.castAdd 3 then 1 else 0) := by
  classical
  change Matrix.J (Fin 3) R (finSumFinEquiv.symm (Fin.natAdd 3 i))
    (finSumFinEquiv.symm j) = _
  rw [finSumFinEquiv_symm_apply_natAdd]
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · rw [finSumFinEquiv_symm_apply_castAdd]
    simp [Matrix.J, Matrix.fromBlocks, Matrix.one_apply, Fin.ext_iff, eq_comm]
  · rw [finSumFinEquiv_symm_apply_natAdd]
    have h : Fin.natAdd 3 j ≠ i.castAdd 3 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
      omega
    have h' : j.addNat 3 ≠ i.castAdd 3 := by
      simpa only [Fin.natAdd_eq_addNat] using h
    simp [Matrix.J, Matrix.fromBlocks, h']

theorem unitEndValue_neg {X : Scheme.{u}}
    (f : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶
      SheafOfModules.unit X.ringCatSheaf) :
    Stacks.FreeSheafMatrix.unitEndValue (-f) = -Stacks.FreeSheafMatrix.unitEndValue f := rfl

theorem symplecticIso_projection_first (X : Scheme.{u}) (i : Fin 3) :
    (symplecticIso X).hom ≫ SheafOfModules.freeProjection (ULift.up.{u} (i.castAdd 3)) =
      -SheafOfModules.freeProjection (ULift.up.{u} (Fin.natAdd 3 i)) := by
  classical
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 6)))
  rintro ⟨j⟩
  apply Stacks.FreeSheafMatrix.unitEndValue_injective
  calc
    _ = Stacks.FreeSheafMatrix.toMatrix (symplecticIso X).hom (i.castAdd 3) j := rfl
    _ = LagrangianTransitivity.standardForm Γ(X,⊤) (i.castAdd 3) j :=
      congrFun (congrFun (Stacks.FreeSheafMatrix.toMatrix_ofMatrix
        (LagrangianTransitivity.standardForm Γ(X,⊤))) (i.castAdd 3)) j
    _ = -(if j = Fin.natAdd 3 i then 1 else 0) := standardForm_first _ i j
    _ = -Stacks.FreeSheafMatrix.unitEndValue
        (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up.{u} j) ≫
          SheafOfModules.freeProjection (ULift.up.{u} (Fin.natAdd 3 i))) :=
      congrArg Neg.neg (Stacks.FreeSheafMatrix.ιFree_comp_freeProjection_value
        (X := X) (Fin.natAdd 3 i) j).symm
    _ = _ := by rw [Preadditive.comp_neg, unitEndValue_neg, SheafOfModules.freeCofan_inj]

theorem symplecticIso_projection_last (X : Scheme.{u}) (i : Fin 3) :
    (symplecticIso X).hom ≫ SheafOfModules.freeProjection (ULift.up.{u} (Fin.natAdd 3 i)) =
      SheafOfModules.freeProjection (ULift.up.{u} (i.castAdd 3)) := by
  classical
  apply Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (ULift.{u} (Fin 6)))
  rintro ⟨j⟩
  apply Stacks.FreeSheafMatrix.unitEndValue_injective
  calc
    _ = Stacks.FreeSheafMatrix.toMatrix (symplecticIso X).hom (Fin.natAdd 3 i) j := rfl
    _ = LagrangianTransitivity.standardForm Γ(X,⊤) (Fin.natAdd 3 i) j :=
      congrFun (congrFun (Stacks.FreeSheafMatrix.toMatrix_ofMatrix
        (LagrangianTransitivity.standardForm Γ(X,⊤))) (Fin.natAdd 3 i)) j
    _ = (if j = i.castAdd 3 then 1 else 0) := standardForm_last _ i j
    _ = _ := (Stacks.FreeSheafMatrix.ιFree_comp_freeProjection_value
      (X := X) (i.castAdd 3) j).symm

variable {X : Scheme.{u}} {Q : X.Modules}

theorem dualEmbedding_projection_first (q : freeOn X 6 ⟶ Q) (i : Fin 3) :
    dualEmbedding q ≫ SheafOfModules.freeProjection (ULift.up.{u} (i.castAdd 3)) =
      -AlgebraicGeometry.dualEvalHom Q (q.app ⊤ (freeBasisSection X 6 (Fin.natAdd 3 i))) := by
  rw [dualEmbedding, Category.assoc, symplecticIso_projection_first,
    Preadditive.comp_neg, pointLineMap_projection]

theorem dualEmbedding_projection_last (q : freeOn X 6 ⟶ Q) (i : Fin 3) :
    dualEmbedding q ≫ SheafOfModules.freeProjection (ULift.up.{u} (Fin.natAdd 3 i)) =
      AlgebraicGeometry.dualEvalHom Q (q.app ⊤ (freeBasisSection X 6 (i.castAdd 3))) := by
  rw [dualEmbedding, Category.assoc, symplecticIso_projection_last, pointLineMap_projection]

/-- Literal actual coordinates on any open of the original free sheaf. -/
def freeCoordinate (r : ℕ) (U : X.Opens) (w : Γ(freeOn X r,U)) (j : Fin r) : Γ(X,U) :=
  Scheme.Modules.Hom.app
    (show freeOn X r ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules) from
      SheafOfModules.freeProjection (ULift.up.{u} j)) U w

theorem dualEmbedding_coordinate_first (q : freeOn X 6 ⟶ Q) (U : X.Opens)
    (α : Γ(dualSheaf Q,U)) (i : Fin 3) :
    freeCoordinate 6 U ((dualEmbedding q).app U α) (i.castAdd 3) =
      -coefficientMap q U α (Fin.natAdd 3 i) := by
  have h := congrArg (fun f : dualSheaf Q ⟶ SheafOfModules.unit X.ringCatSheaf => f.app U α)
    (dualEmbedding_projection_first q i)
  change freeCoordinate 6 U ((dualEmbedding q).app U α) (i.castAdd 3) =
    -coefficientMap q U α (Fin.natAdd 3 i) at h
  exact h

theorem dualEmbedding_coordinate_last (q : freeOn X 6 ⟶ Q) (U : X.Opens)
    (α : Γ(dualSheaf Q,U)) (i : Fin 3) :
    freeCoordinate 6 U ((dualEmbedding q).app U α) (Fin.natAdd 3 i) =
      coefficientMap q U α (i.castAdd 3) := by
  have h := congrArg (fun f : dualSheaf Q ⟶ SheafOfModules.unit X.ringCatSheaf => f.app U α)
    (dualEmbedding_projection_last q i)
  change freeCoordinate 6 U ((dualEmbedding q).app U α) (Fin.natAdd 3 i) =
    coefficientMap q U α (i.castAdd 3) at h
  exact h

end M9Native.SymplecticQuotientCoordinates
