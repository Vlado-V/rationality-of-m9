module

public import M9StacksIntegration.MukaiEvaluationChoices
public import M9StacksIntegration.SplitMatrixGrassmannianNaturality
public import M9StacksIntegration.LagrangianSymplecticAction
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyLinear

/-!
# Constant matrices acting on the original complete evaluation

The source free-sheaf map is the actual matrix with coefficients pulled
through the original structure morphism.  Its effect on complete evaluation
is computed on the original native basis sections. Nonzero scalar target
maps are actual isomorphisms of the original sheaves.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiEvaluationMatrix

open MukaiLagrangianMap MukaiEvaluationChoices LagrangianMatrixChart

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

def scalarIso (E : X.Modules) (a : k) (ha : a ≠ 0) : E ≅ E := by
  letI := modulesLinearOverField k f
  exact
  { hom := a • 𝟙 E
    inv := a⁻¹ • 𝟙 E
    hom_inv_id := by simp [Linear.comp_smul, smul_smul, ha]
    inv_hom_id := by simp [Linear.comp_smul, smul_smul, ha] }

theorem h0_scalarIso (E : X.Modules) (a : k) (ha : a ≠ 0) (s : H0 k f E) :
    cohomologyOverFieldMap k f (scalarIso k f E a ha).hom 0 s = a • s := by
  let := modulesLinearOverField k f
  change cohomologyOverFieldMap k f (a • 𝟙 E) 0 s = a • s
  rw [cohomologyOverFieldMap_smul, cohomologyOverFieldMap_id]
  rfl

theorem evaluation_scalarIso {r : ℕ} (E : X.Modules) (s : Fin r → H0 k f E)
    (a : k) (ha : a ≠ 0) :
    MukaiSemiIrreducible.evaluation k f E s ≫ (scalarIso k f E a ha).hom =
      MukaiSemiIrreducible.evaluation k f E (fun i => a • s i) := by
  rw [evaluation_postcomp]
  congr 1
  funext i
  exact h0_scalarIso k f E a ha (s i)

theorem freeHomEquiv_top {r : ℕ} {E : X.Modules}
    (q : freeOn X r ⟶ E) (i : Fin r) :
    (E.freeHomEquiv q (ULift.up.{u} i)).eval (op ⊤) =
      q.app ⊤ (freeBasisSection X r i) := by
  rw [SheafOfModules.freeHomEquiv_apply]
  change q.app ⊤ ((SheafOfModules.freeSection (R := X.ringCatSheaf)
    (ULift.up.{u} i)).eval (op ⊤)) = _
  congr 1

/-- Actual morphisms from the original free sheaf are determined by their
values on the literal standard global sections. -/
theorem freeHom_ext_top {r : ℕ} {E : X.Modules} (q q' : freeOn X r ⟶ E)
    (h : ∀ i : Fin r, q.app ⊤ (freeBasisSection X r i) =
      q'.app ⊤ (freeBasisSection X r i)) : q = q' := by
  apply E.freeHomEquiv.injective
  funext i
  rcases i with ⟨i⟩
  apply Stacks.PresheafOfModules.sections_ext_top
  change (E.freeHomEquiv q (ULift.up.{u} i)).eval (op ⊤) =
    (E.freeHomEquiv q' (ULift.up.{u} i)).eval (op ⊤)
  rw [freeHomEquiv_top, freeHomEquiv_top]
  exact h i

theorem evaluation_basisSection {r : ℕ} (E : X.Modules) (s : Fin r → H0 k f E)
    (i : Fin r) :
    (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation k f E s) ⊤) (freeBasisSection X r i) =
      ExteriorEvaluation.h0SectionsSemilinear k f E (s i) := by
  change (MukaiSemiIrreducible.evaluation k f E s).val.app (op ⊤)
    (freeBasisSection X r i) = (cohomologyOverFieldZeroLinearIso k f E).hom (s i)
  simpa [freeBasisSection, SheafOfModules.freeSection, SheafOfModules.freeHomEquiv,
    Category.comp_id] using TupleEvaluationFiber.evaluation_freeSection_top k f E s i

def constantMap {r : ℕ} (M : Matrix (Fin r) (Fin r) k) : freeOn X r ⟶ freeOn X r :=
  Stacks.FreeSheafMatrix.ofMatrix (M.map (ExteriorEvaluation.baseRingMap k f))

theorem constantMap_matrix {r : ℕ} (M : Matrix (Fin r) (Fin r) k) :
    Stacks.FreeSheafMatrix.toMatrix (constantMap k f M) =
      M.map (ExteriorEvaluation.baseRingMap k f) := Stacks.FreeSheafMatrix.toMatrix_ofMatrix _

/-- Precomposition by the actual constant matrix evaluates its actual
linear combinations in the original complete section basis. -/
theorem evaluation_precomp_matrix {r : ℕ} (E : X.Modules)
    (b : Basis (Fin r) k (H0 k f E)) (M : Matrix (Fin r) (Fin r) k) :
    constantMap k f M ≫ MukaiSemiIrreducible.evaluation k f E b =
      MukaiSemiIrreducible.evaluation k f E (fun j => b.equivFun.symm (M.col j)) := by
  apply freeHom_ext_top
  intro j
  change (Scheme.Modules.Hom.app (MukaiSemiIrreducible.evaluation k f E b) ⊤)
    ((constantMap k f M).app ⊤ (freeBasisSection X r j)) = _
  rw [SplitMatrixGrassmannianNaturality.freeMap_column_eq_sum]
  simp only [constantMap_matrix, Matrix.map_apply, map_sum,
    Scheme.Modules.Hom.app_smul, evaluation_basisSection]
  let v := b.equivFun.symm (M.col j)
  have hc (i : Fin r) : b.repr v i = M i j := by
    have h := congrFun (b.equivFun.apply_symm_apply (M.col j)) i
    exact h
  have hs : ∑ i : Fin r, M i j • b i = v := by
    simpa only [hc] using b.sum_repr v
  have h := congrArg (ExteriorEvaluation.h0SectionsSemilinear k f E) hs
  simpa only [map_sum, map_smulₛₗ] using h

theorem baseRingMap_eq_scalarMap :
    ExteriorEvaluation.baseRingMap k f = LagrangianSymplecticAction.scalarMap k f := by
  have happ : f.appLE ⊤ ⊤ (by simp) = f.appTop := by
    have h : X.presheaf.map (homOfLE (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ by simp)).op =
        𝟙 Γ(X, ⊤) := by
      change X.presheaf.map (𝟙 (op (⊤ : X.Opens))) = _
      exact X.presheaf.map_id _
    rw [Scheme.Hom.appLE, h]
    exact Category.comp_id _
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom =
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom
  rw [happ]

/-- The constant source map is literally the free automorphism used by
the original native LG action. -/
theorem constantFreeIso_eq_constantMap (g : Matrix.symplecticGroup (Fin 3) k) :
    (LagrangianSymplecticAction.constantFreeIso k f g).hom =
      constantMap k f (LagrangianTransitivity.matrixSix k g) := by
  apply Stacks.FreeSheafMatrix.toMatrix_injective
  rw [LagrangianSymplecticAction.constantFreeIso_matrix, constantMap_matrix,
    LagrangianSymplecticAction.constantMatrix, baseRingMap_eq_scalarMap]

end M9Native.MukaiEvaluationMatrix
