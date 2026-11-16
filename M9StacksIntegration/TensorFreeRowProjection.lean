module

public import M9StacksIntegration.TensorFreeCoordinates
public import M9StacksIntegration.NativeHomScalars
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap

/-!
# Actual split line projections of a nonzero original row

A literal base-field row defines an actual map from a line times the
original finite free sheaf to the line. A nonzero entry gives an actual
right inverse. Its actual sheaf dual is therefore split injective,
before any curve, fibre, or conormal argument.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.TensorFreeRowProjection

open LagrangianMatrixChart LinearIncidenceTensorCoordinates

variable {X : Scheme.{u}} (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

variable (L : X.Modules) (r : ℕ)

/-- The original tensor coordinate inclusions and projections have the genuine delta relation. -/
theorem inclusion_comp_projection (i j : Fin r) :
    TensorFreeCoordinates.inclusion X L r (ULift.up i) ≫
      TensorFreeCoordinates.projection X L r (ULift.up j) =
        if i = j then 𝟙 L else 0 := by
  classical
  calc
    _ = (TensorFreeCoordinates.rightUnit X L).inv ≫
      (TensorFreeCoordinates.tensorFunctor X L).map
        (SheafOfModules.ιFree (R := X.ringCatSheaf) (ULift.up i : ULift.{u} (Fin r)) ≫
          SheafOfModules.freeProjection (ULift.up j)) ≫
      (TensorFreeCoordinates.rightUnit X L).hom := by
        simp only [TensorFreeCoordinates.inclusion, TensorFreeCoordinates.projection,
          Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [SheafOfModules.ιFree_comp_freeProjection]
      by_cases h : i = j
      · rw [if_pos (congrArg ULift.up h), CategoryTheory.Functor.map_id, Category.id_comp,
          Iso.inv_hom_id, if_pos h]
      · have hu : (ULift.up i : ULift.{u} (Fin r)) ≠ ULift.up j :=
          fun he => h (ULift.up_inj.mp he)
        rw [if_neg hu, CategoryTheory.Functor.map_zero, Limits.zero_comp, Limits.comp_zero, if_neg h]

/-- The literal original row, using precisely the original structural scalar action. -/
def row (a : Fin r → k) : tensorObj X L (freeOn X r) ⟶ L := by
  letI := modulesLinearOverField k f
  exact ∑ i : Fin r, a i • TensorFreeCoordinates.projection X L r (ULift.up i)

/-- Actual coefficient multiplication on a sheaf morphism, on every original open. -/
theorem smul_hom_app {A B : X.Modules} (c : k) (g : A ⟶ B)
    (U : X.Opens) (s : Γ(A, U)) :
    letI := modulesLinearOverField k f
    (c • g).app U s =
      (show Γ(X,U) from baseRingToSections k (Over.mk f) (op U) c) • g.app U s := by
  letI := modulesLinearOverField k f
  change (g.val.app (op U)).hom
    ((show Γ(X,U) from baseRingToSections k (Over.mk f) (op U) c) • s) = _
  exact (g.val.app (op U)).hom.map_smul _ _

/-- The actual row has the actual original coefficient values on all sections. -/
theorem row_app (a : Fin r → k) (U : X.Opens)
    (s : Γ(tensorObj X L (freeOn X r), U)) :
    (row k f L r a).app U s =
      ∑ i : Fin r, (show Γ(X,U) from baseRingToSections k (Over.mk f) (op U) (a i)) •
        (TensorFreeCoordinates.projection X L r (ULift.up i)).app U s := by
  letI := modulesLinearOverField k f
  rw [row, SectionZeroIdealFactorization.sum_app_apply]
  exact Finset.sum_congr rfl fun i _ => smul_hom_app k f (a i) _ U s

/-- An actual coordinate line inclusion reads off the literal original row entry. -/
theorem inclusion_comp_row (a : Fin r → k) (j : Fin r) :
    letI := modulesLinearOverField k f
    TensorFreeCoordinates.inclusion X L r (ULift.up j) ≫ row k f L r a = a j • 𝟙 L := by
  classical
  letI := modulesLinearOverField k f
  simp [row, Preadditive.comp_sum, Linear.comp_smul, inclusion_comp_projection]

/-- A nonzero original base-field row gives a genuine split line quotient. -/
theorem exists_rightInverse (a : Fin r → k) (ha : a ≠ 0) :
    ∃ t : L ⟶ tensorObj X L (freeOn X r), t ≫ row k f L r a = 𝟙 L := by
  classical
  letI := modulesLinearOverField k f
  obtain ⟨j, hj⟩ : ∃ j : Fin r, a j ≠ 0 := by
    by_contra hn
    apply ha
    ext j
    exact not_not.mp (not_exists.mp hn j)
  refine ⟨(a j)⁻¹ • TensorFreeCoordinates.inclusion X L r (ULift.up j), ?_⟩
  rw [Linear.smul_comp, inclusion_comp_row, smul_smul, inv_mul_cancel₀ hj, one_smul]

/-- The genuine sheaf dual of a nonzero original row is split injective. -/
theorem dual_exists_leftInverse (a : Fin r → k) (ha : a ≠ 0) :
    ∃ t : dualSheaf (tensorObj X L (freeOn X r)) ⟶ dualSheaf L,
      dualMap (row k f L r a) ≫ t = 𝟙 (dualSheaf L) := by
  obtain ⟨t, ht⟩ := exists_rightInverse k f L r a ha
  exact ⟨dualMap t, (dualMap_comp t (row k f L r a)).symm.trans
    ((congrArg dualMap ht).trans (dualMap_id L))⟩

/-- On original tensor equations, this row is the literal row combination of original line sections. -/
theorem row_rowTensor {n : ℕ} (q : freeOn X n ⟶ freeOn X r)
    (s : Fin n → Γ(L,⊤)) (a : Fin r → k) :
    (row k f L r a).app ⊤ (TensorFreeCoordinates.rowTensor X L r q s) =
      ∑ i : Fin r, (show Γ(X,⊤) from baseRingToSections k (Over.mk f) (op ⊤) (a i)) •
        (∑ j : Fin n, Stacks.FreeSheafMatrix.toMatrix q i j • s j) := by
  rw [row_app]
  simp only [TensorFreeCoordinates.projection_rowTensor]

end M9Native.TensorFreeRowProjection
