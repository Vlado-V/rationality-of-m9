module

public import M9StacksIntegration.LagrangianSigmaInvariance

/-! Canonical pullback of actual free-six endomorphisms acts on their genuine
coefficient matrices by the actual map on global functions. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

namespace M9Native.LagrangianFreeMatrixPullback

open M9Native.LagrangianMatrixChart M9Native.LagrangianGrassmannian
open AlgebraicGeometry.Grassmannian M9Native.SectionZeroIdealFactorization

theorem freeCoordinates_basis (X : Scheme.{u}) (n : ℕ) (i j : Fin n) :
    freeSectionCoordinates X n (freeBasisSection X n j) i=if i=j then 1 else 0 := by
  have h := freeCoordinates_map_basis (𝟙 (freeOn X n)) i j
  have hid : Stacks.FreeSheafMatrix.toMatrix (𝟙 (freeOn X n))=1 :=
    Stacks.FreeSheafMatrix.toMatrix_id (X:=X) n
  rw [hid,Matrix.one_apply,Scheme.Modules.Hom.id_app,ConcreteCategory.id_apply] at h
  exact h

theorem freeCoordinates_freeVector (X : Scheme.{u}) (i j : Fin 6) :
    freeSectionCoordinates X 6 (freeVector X j) i=if i=j then 1 else 0 :=
  freeCoordinates_basis X 6 i j

theorem eq_sum_coordinates_basis (X : Scheme.{u}) (n : ℕ) (s : Γ(freeOn X n,⊤)) :
    s=∑ i : Fin n, freeSectionCoordinates X n s i • freeBasisSection X n i := by
  apply (freeSectionCoordinates X n).injective
  funext j
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,freeCoordinates_basis]
  simp

theorem end_column_eq_sum (X : Scheme.{u}) (a : freeOn X 6 ⟶ freeOn X 6) (j : Fin 6) :
    a.app ⊤ (freeVector X j)=
      ∑ i : Fin 6, Stacks.FreeSheafMatrix.toMatrix a i j • freeVector X i := by
  have hc (i : Fin 6) : freeSectionCoordinates X 6 (a.app ⊤ (freeVector X j)) i=
      Stacks.FreeSheafMatrix.toMatrix a i j := freeCoordinates_map_basis a i j
  have h := eq_sum_coordinates_basis X 6 (a.app ⊤ (freeVector X j))
  change a.app ⊤ (freeVector X j)=∑ i : Fin 6,
    freeSectionCoordinates X 6 (a.app ⊤ (freeVector X j)) i • freeVector X i at h
  simpa only [hc] using h

def pulledFreeEnd {X Y : Scheme.{u}} (f : Y ⟶ X) (a : freeOn X 6 ⟶ freeOn X 6) :
    freeOn Y 6 ⟶ freeOn Y 6 :=
  (pullbackFreeIso f 6).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackFreeIso f 6).hom

theorem inverse_freeVector_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (j : Fin 6) :
    (pullbackFreeIso f 6).inv.app ⊤ (freeVector Y j)=
      pullbackGlobalSections f (freeOn X 6) (freeVector X j) := by
  have h := congrArg ((pullbackFreeIso f 6).inv.app ⊤) (freeVector_pullback f j)
  change ((pullbackFreeIso f 6).hom ≫ (pullbackFreeIso f 6).inv).app ⊤
    (pullbackGlobalSections f (freeOn X 6) (freeVector X j))=_ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

theorem pulledFreeEnd_column {X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : freeOn X 6 ⟶ freeOn X 6) (j : Fin 6) :
    (pulledFreeEnd f a).app ⊤ (freeVector Y j)=
      ∑ i : Fin 6,f.appTop (Stacks.FreeSheafMatrix.toMatrix a i j) • freeVector Y i := by
  change (pullbackFreeIso f 6).hom.app ⊤
    (((Scheme.Modules.pullback f).map a).app ⊤
      ((pullbackFreeIso f 6).inv.app ⊤ (freeVector Y j)))=_
  rw [inverse_freeVector_pullback,pullback_map_app_pullbackGlobalSections,end_column_eq_sum]
  simp only [map_sum,AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul,
    freeVector_pullback]

/-- The actual canonical pullback acts entrywise on the genuine coefficient matrix. -/
theorem pulledFreeEnd_matrix {X Y : Scheme.{u}} (f : Y ⟶ X)
    (a : freeOn X 6 ⟶ freeOn X 6) :
    Stacks.FreeSheafMatrix.toMatrix (pulledFreeEnd f a)=
      (Stacks.FreeSheafMatrix.toMatrix a).map f.appTop.hom := by
  ext i j
  rw [← freeCoordinates_map_basis (pulledFreeEnd f a) i j]
  change freeSectionCoordinates Y 6 ((pulledFreeEnd f a).app ⊤ (freeVector Y j)) i=_
  rw [pulledFreeEnd_column]
  simp only [map_sum,map_smul,Finset.sum_apply,Pi.smul_apply,freeCoordinates_freeVector]
  simp

end M9Native.LagrangianFreeMatrixPullback

end
