module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafTensorAdditiveOnOpens
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorBilinear

/-! Genuine global coordinates of A tensor a finite free sheaf.
The coordinate projections and inclusions are actual sheaf morphisms and
their decomposition of the identity proves the section-vanishing criterion.
No line trivialization, local frame, or invertibility premise is needed. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.LinearIncidenceTensorCoordinates M9Native.LagrangianMatrixChart
open M9Native.SectionZeroIdealFactorization
open scoped BigOperators TensorProduct

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive

namespace M9Native.TensorFreeCoordinates

private theorem linear_tmul_smul {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (g : (M ⊗[R] N) →ₗ[R] P)
    (c : R) (s : M) (t : N) : g (s ⊗ₜ[R] (c • t)) = c • g (s ⊗ₜ[R] t) := by
  rw [TensorProduct.tmul_smul, map_smul]

variable (X : Scheme.{u}) (A : X.Modules) (r : ℕ)

abbrev tensorFunctor := (Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).obj A

instance tensorFunctor_additive : (tensorFunctor X A).Additive := by
  exact Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive X.sheaf A

def rightUnit : tensorObj X A (SheafOfModules.unit X.ringCatSheaf) ≅ A :=
  Stacks.SheafOfModules.Invertible.tensorProductRightUnitor X.sheaf.obj X.ringCatSheaf.property A

def projection (i : ULift.{u} (Fin r)) : tensorObj X A (freeOn X r) ⟶ A :=
  (tensorFunctor X A).map (SheafOfModules.freeProjection i) ≫ (rightUnit X A).hom

def inclusion (i : ULift.{u} (Fin r)) : A ⟶ tensorObj X A (freeOn X r) :=
  (rightUnit X A).inv ≫ (tensorFunctor X A).map (SheafOfModules.ιFree i)

theorem sum_projection_inclusion :
    ∑ i : ULift.{u} (Fin r), projection X A r i ≫ inclusion X A r i =
      𝟙 (tensorObj X A (freeOn X r)) := by
  let _ := tensorFunctor_additive X A
  simp only [projection, inclusion, Category.assoc, Iso.hom_inv_id_assoc,
    ← Functor.map_comp]
  rw [← Functor.map_sum (F := tensorFunctor X A),
    SheafOfModules.sum_freeProjection_comp_ιFree, CategoryTheory.Functor.map_id]

theorem section_eq_sum (s : Γ(tensorObj X A (freeOn X r), ⊤)) :
    s = ∑ i : ULift.{u} (Fin r),
      (inclusion X A r i).app ⊤ ((projection X A r i).app ⊤ s) := by
  have h := congrArg (fun φ : tensorObj X A (freeOn X r) ⟶ tensorObj X A (freeOn X r) =>
    φ.app ⊤ s) (sum_projection_inclusion X A r)
  rw [sum_app_apply] at h
  exact h.symm

theorem section_zero_iff (s : Γ(tensorObj X A (freeOn X r), ⊤)) :
    s = 0 ↔ ∀ i : ULift.{u} (Fin r), (projection X A r i).app ⊤ s = 0 := by
  constructor
  · intro h i
    rw [h, map_zero]
  · intro h
    rw [section_eq_sum X A r s]
    exact Finset.sum_eq_zero fun i _ => by rw [h i, map_zero]

theorem tensorTop_smul_right (B : X.Modules) (c : Γ(X, ⊤))
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    tensorTop X A B s (c • t) = c • tensorTop X A B s t := by
  unfold tensorTop Stacks.SheafOfModules.tensorSectionsAt
  exact linear_tmul_smul
    (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
      X.ringCatSheaf.property (PresheafOfModules.tensorObj A.val B.val)).app (op ⊤)).hom) c s t

theorem rightUnit_apply (s : Γ(A, ⊤)) (c : Γ(X, ⊤)) :
    (rightUnit X A).hom.app ⊤
      (tensorTop X A (SheafOfModules.unit X.ringCatSheaf) s c) = c • s := by
  calc
    _ = (rightUnit X A).hom.app ⊤
        (tensorTop X A (SheafOfModules.unit X.ringCatSheaf) s
          (c • (1 : Γ(X, ⊤)))) := by simp
    _ = c • (rightUnit X A).hom.app ⊤
        (tensorTop X A (SheafOfModules.unit X.ringCatSheaf) s (1 : Γ(X, ⊤))) := by
      rw [tensorTop_smul_right, Scheme.Modules.Hom.app_smul]
    _ = c • s := congrArg (fun z => c • z)
      (Stacks.SheafOfModules.tensorSections_rightUnitorAt X.sheaf.obj X.ringCatSheaf.property
        (op ⊤) A s)

theorem tensorFunctor_map_tensorTop {B C : X.Modules} (g : B ⟶ C)
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    ((tensorFunctor X A).map g).val.app (op ⊤) (tensorTop X A B s t) =
      tensorTop X A C s (g.app ⊤ t) := by
  refine (Stacks.SheafOfModules.toSheafify_app_map_obj
    (O := X.sheaf.obj) (hO := X.ringCatSheaf.property)
    (f := PresheafOfModules.tensorHom (O := X.sheaf.obj) (𝟙 A.val) g.val)
    (op ⊤) (s ⊗ₜ t)).trans ?_
  exact congrArg (fun z =>
    (Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj X.ringCatSheaf.property
      (PresheafOfModules.tensorObj A.val C.val)).app (op ⊤) z)
    (PresheafOfModules.tensorHom_tmul (O := X.sheaf.obj) (𝟙 A.val) g.val (op ⊤) s t)

theorem projection_tensorTop (i : ULift.{u} (Fin r)) (s : Γ(A, ⊤))
    (t : Γ(freeOn X r, ⊤)) :
    (projection X A r i).app ⊤ (tensorTop X A (freeOn X r) s t) =
      freeSectionCoordinates X r t i.down • s := by
  change (rightUnit X A).hom.app ⊤
    (((tensorFunctor X A).map (SheafOfModules.freeProjection i)).val.app (op ⊤)
      (tensorTop X A (freeOn X r) s t)) = _
  rw [tensorFunctor_map_tensorTop]
  change (rightUnit X A).hom.app ⊤
    (tensorTop X A (SheafOfModules.unit X.ringCatSheaf) s
      ((SheafOfModules.freeProjection (R := X.ringCatSheaf) i).val.app (op ⊤) t)) = _
  rw [rightUnit_apply]
  cases i with
  | up i => rw [freeSectionCoordinates_apply, freeProj_eq_freeProjection]

def rowTensor {n : ℕ} (q : freeOn X n ⟶ freeOn X r) (s : Fin n → Γ(A, ⊤)) :
    Γ(tensorObj X A (freeOn X r), ⊤) :=
  ∑ i : Fin n, tensorTop X A (freeOn X r) (s i) (q.app ⊤ (freeBasisSection X n i))

theorem projection_rowTensor {n : ℕ} (q : freeOn X n ⟶ freeOn X r)
    (s : Fin n → Γ(A, ⊤)) (i : ULift.{u} (Fin r)) :
    (projection X A r i).app ⊤ (rowTensor X A r q s) =
      ∑ j : Fin n, Stacks.FreeSheafMatrix.toMatrix q i.down j • s j := by
  simp only [rowTensor, map_sum, projection_tensorTop, freeBasisSection,
    freeCoordinates_map_basis]

/-- Actual tensor-section vanishing is exactly vanishing of the literal
matrix row combinations of the original sections, globally. -/
theorem rowTensor_zero_iff {n : ℕ} (q : freeOn X n ⟶ freeOn X r)
    (s : Fin n → Γ(A, ⊤)) :
    rowTensor X A r q s = 0 ↔
      ∀ i : Fin r, (∑ j : Fin n, Stacks.FreeSheafMatrix.toMatrix q i j • s j) = 0 := by
  constructor
  · intro h i
    have hi := (section_zero_iff X A r _).mp h (ULift.up i)
    rwa [projection_rowTensor] at hi
  · intro h
    apply (section_zero_iff X A r _).mpr
    rintro ⟨i⟩
    rw [projection_rowTensor]
    exact h i

end M9Native.TensorFreeCoordinates
