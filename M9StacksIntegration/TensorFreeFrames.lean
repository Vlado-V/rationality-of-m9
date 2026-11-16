module

public import M9StacksIntegration.TensorFreeCoordinates

/-! Genuine quotient frames in the global tensor-row criterion, and
their actual pullback-tensor comparison. The first factor is arbitrary;
there is no line-frame or prescribed coefficient equality premise. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open M9Native.LinearIncidenceTensorCoordinates M9Native.LagrangianMatrixChart
open M9Native.TensorFreeCoordinates
open scoped BigOperators

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.SheafedSpace.sheaf Stacks.SheafOfModules.Tensor.ringSheaf
  Stacks.SheafOfModules.TensorSheafification.structureSheaf

namespace M9Native.TensorFreeFrames

variable (X : Scheme.{u}) (A B : X.Modules) (r : ℕ)

def frameIso (d : B ≅ freeOn X r) : tensorObj X A B ≅ tensorObj X A (freeOn X r) :=
  (tensorFunctor X A).mapIso d

def rowTensor {n : ℕ} (q : freeOn X n ⟶ B) (s : Fin n → Γ(A, ⊤)) :
    Γ(tensorObj X A B, ⊤) :=
  ∑ i : Fin n, tensorTop X A B (s i) (q.app ⊤ (freeBasisSection X n i))

theorem frameIso_rowTensor {n : ℕ} (d : B ≅ freeOn X r)
    (q : freeOn X n ⟶ B) (s : Fin n → Γ(A, ⊤)) :
    (frameIso X A B r d).hom.app ⊤ (rowTensor X A B q s) =
      TensorFreeCoordinates.rowTensor X A r (q ≫ d.hom) s := by
  simp only [rowTensor, TensorFreeCoordinates.rowTensor, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact tensorFunctor_map_tensorTop X A d.hom (s i) (q.app ⊤ (freeBasisSection X n i))

theorem rowTensor_zero_iff {n : ℕ} (d : B ≅ freeOn X r)
    (q : freeOn X n ⟶ B) (s : Fin n → Γ(A, ⊤)) :
    rowTensor X A B q s = 0 ↔
      ∀ i : Fin r, (∑ j : Fin n, Stacks.FreeSheafMatrix.toMatrix (q ≫ d.hom) i j • s j) = 0 := by
  rw [← TensorFreeCoordinates.rowTensor_zero_iff X A r (q ≫ d.hom) s,
    ← frameIso_rowTensor X A B r d q s]
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((frameIso X A B r d).hom.app ⊤)).injective).symm

def pullbackFrameIso {Y : Scheme.{u}} (f : Y ⟶ X)
    (d : (Scheme.Modules.pullback f).obj B ≅ freeOn Y r) :
    (Scheme.Modules.pullback f).obj (tensorObj X A B) ≅
      tensorObj Y ((Scheme.Modules.pullback f).obj A) (freeOn Y r) :=
  Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B ≪≫
    (tensorFunctor Y ((Scheme.Modules.pullback f).obj A)).mapIso d

theorem pullbackFrameIso_tensorTop {Y : Scheme.{u}} (f : Y ⟶ X)
    (d : (Scheme.Modules.pullback f).obj B ≅ freeOn Y r)
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    (pullbackFrameIso X A B r f d).hom.app ⊤
      (pullbackGlobalSections f (tensorObj X A B) (tensorTop X A B s t)) =
    tensorTop Y ((Scheme.Modules.pullback f).obj A) (freeOn Y r)
      (pullbackGlobalSections f A s) (d.hom.app ⊤ (pullbackGlobalSections f B t)) := by
  refine (congrArg (fun z =>
    ((tensorFunctor Y ((Scheme.Modules.pullback f).obj A)).map d.hom).val.app (op ⊤) z)
    (Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B s t)).trans ?_
  exact tensorFunctor_map_tensorTop Y ((Scheme.Modules.pullback f).obj A) d.hom _ _

end M9Native.TensorFreeFrames
