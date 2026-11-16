module

public import M9StacksIntegration.LagrangianFreeMatrixPullback

/-! Canonical pullback carries actual free-bundle matrices entrywise for every rank. -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

namespace M9Native.PrimitiveFreeMatrixPullback

open LagrangianMatrixChart LagrangianGrassmannian LagrangianFreeMatrixPullback
open AlgebraicGeometry.Grassmannian SectionZeroIdealFactorization

theorem freeBasisSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) (i : Fin n) :
    (pullbackFreeIso f n).hom.app ⊤
      (pullbackGlobalSections f (freeOn X n) (freeBasisSection X n i)) =
        freeBasisSection Y n i := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have hnat := pullback_map_app_pullbackGlobalSections f
    (SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up.{u} i)) (1 : Γ(X,⊤))
  have hcomp := congrArg (fun φ => φ.val.app (op ⊤)
    (pullbackGlobalSections f (SheafOfModules.unit X.ringCatSheaf) (1 : Γ(X,⊤))))
      (pullback_map_ιFree_comp_pullbackFreeIso_hom f n (ULift.up.{u} i))
  change (pullbackFreeIso f n).hom.app ⊤
    (pullbackGlobalSections f (freeOn X n)
      ((SheafOfModules.ιFree (R:=X.ringCatSheaf) (ULift.up.{u} i)).val.app (op ⊤)
        (1 : Γ(X,⊤)))) = _
  exact (congrArg ((pullbackFreeIso f n).hom.app ⊤) hnat.symm).trans
    (hcomp.trans (congrArg
      ((SheafOfModules.ιFree (R:=Y.ringCatSheaf) (ULift.up.{u} i)).val.app (op ⊤))
      (unit_pullback_one f)))

theorem inverse_freeBasisSection_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (j : Fin n) :
    (pullbackFreeIso f n).inv.app ⊤ (freeBasisSection Y n j) =
      pullbackGlobalSections f (freeOn X n) (freeBasisSection X n j) := by
  have h := congrArg ((pullbackFreeIso f n).inv.app ⊤) (freeBasisSection_pullback f n j)
  change ((pullbackFreeIso f n).hom ≫ (pullbackFreeIso f n).inv).app ⊤
    (pullbackGlobalSections f (freeOn X n) (freeBasisSection X n j)) = _ at h
  rw [Iso.hom_inv_id] at h
  exact h.symm

theorem end_column_eq_sum (X : Scheme.{u}) (n : ℕ) (a : freeOn X n ⟶ freeOn X n)
    (j : Fin n) :
    a.app ⊤ (freeBasisSection X n j) =
      ∑ i : Fin n, Stacks.FreeSheafMatrix.toMatrix a i j • freeBasisSection X n i := by
  have hc (i : Fin n) : freeSectionCoordinates X n (a.app ⊤ (freeBasisSection X n j)) i =
      Stacks.FreeSheafMatrix.toMatrix a i j := freeCoordinates_map_basis a i j
  have h := eq_sum_coordinates_basis X n (a.app ⊤ (freeBasisSection X n j))
  simpa only [hc] using h

def pulledFreeEnd {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (a : freeOn X n ⟶ freeOn X n) : freeOn Y n ⟶ freeOn Y n :=
  (pullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map a ≫ (pullbackFreeIso f n).hom

theorem pulledFreeEnd_column {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (a : freeOn X n ⟶ freeOn X n) (j : Fin n) :
    (pulledFreeEnd f n a).app ⊤ (freeBasisSection Y n j) =
      ∑ i : Fin n, f.appTop (Stacks.FreeSheafMatrix.toMatrix a i j) • freeBasisSection Y n i := by
  change (pullbackFreeIso f n).hom.app ⊤
    (((Scheme.Modules.pullback f).map a).app ⊤
      ((pullbackFreeIso f n).inv.app ⊤ (freeBasisSection Y n j))) = _
  rw [inverse_freeBasisSection_pullback, pullback_map_app_pullbackGlobalSections, end_column_eq_sum]
  simp only [map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, freeBasisSection_pullback]

theorem pulledFreeEnd_matrix {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (a : freeOn X n ⟶ freeOn X n) :
    Stacks.FreeSheafMatrix.toMatrix (pulledFreeEnd f n a) =
      (Stacks.FreeSheafMatrix.toMatrix a).map f.appTop.hom := by
  ext i j
  rw [← freeCoordinates_map_basis (pulledFreeEnd f n a) i j]
  change freeSectionCoordinates Y n ((pulledFreeEnd f n a).app ⊤ (freeBasisSection Y n j)) i = _
  rw [pulledFreeEnd_column]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis]
  simp

end M9Native.PrimitiveFreeMatrixPullback
