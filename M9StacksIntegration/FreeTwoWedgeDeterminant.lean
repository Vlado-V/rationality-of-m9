module

public import M9StacksIntegration.LagrangianSigmaInvariance

/-! An actual free frame of a rank-two sheaf sends its actual exterior
pair section to the literal determinant of its two coordinate columns.
The comparison is valid on arbitrary schemes and over rings with
nilpotents. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
universe u
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  AlgebraicGeometry.Scheme.Modules.presheaf AlgebraicGeometry.SheafedSpace.sheaf

namespace M9Native.FreeTwoWedgeDeterminant
open LagrangianMatrixChart

private theorem coordinate_pair {R : Type u} [CommRing R] (s t : Fin 2 → R) :
    exteriorPower.pairingDual R (Fin 2 → R) 2
      (exteriorPower.ιMulti R 2 ![LinearMap.proj 0,LinearMap.proj 1])
      (exteriorPower.ιMulti R 2 ![s,t]) = s 0 * t 1 - s 1 * t 0 := by
  simp only [exteriorPower.pairingDual_ιMulti_ιMulti,Matrix.det_fin_two,
    Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,LinearMap.proj_apply]

private theorem equiv_function_eval {R V W : Type u} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (e : V ≃ₗ[R] W) (d : V →ₗ[R] R) (v : V) :
    (d.comp e.symm.toLinearMap) (e v) = d v := by
  exact congrArg d (e.symm_apply_apply v)

variable (X : Scheme.{u})

def determinantCoordinate : Γ(Scheme.Modules.exteriorPower (freeOn X 2) (2 : ℤ),⊤)
    →ₗ[Γ(X,⊤)] Γ(X,⊤) :=
  (exteriorPower.pairingDual Γ(X,⊤) (Fin 2 → Γ(X,⊤)) 2
    (exteriorPower.ιMulti Γ(X,⊤) 2 ![LinearMap.proj 0, LinearMap.proj 1])).comp
      (freeExteriorSectionsEquiv X 2 2).symm.toLinearMap

theorem determinantCoordinate_wedge (s t : Γ(freeOn X 2,⊤)) :
    determinantCoordinate X (LagrangianGrassmannian.wedgeSection X (freeOn X 2) s t) =
      freeSectionCoordinates X 2 s 0 * freeSectionCoordinates X 2 t 1 -
        freeSectionCoordinates X 2 s 1 * freeSectionCoordinates X 2 t 0 := by
  have he : (fun i : Fin 2 => (freeSectionCoordinates X 2).symm
      (![freeSectionCoordinates X 2 s, freeSectionCoordinates X 2 t] i)) = ![s,t] := by
    funext i
    have hi : i=0 ∨ i=1 := by omega
    rcases hi with rfl | rfl <;> simp
  have hw := freeExteriorSectionsEquiv_ιMulti X 2 2
    ![freeSectionCoordinates X 2 s, freeSectionCoordinates X 2 t]
  rw [he] at hw
  have hsw := (LagrangianSigmaInvariance.wedgeSection_eq_comparison X (freeOn X 2) s t).trans hw.symm
  have h1 := congrArg (determinantCoordinate X) hsw
  have h2 := equiv_function_eval (freeExteriorSectionsEquiv X 2 2)
    (exteriorPower.pairingDual Γ(X,⊤) (Fin 2 → Γ(X,⊤)) 2
      (exteriorPower.ιMulti Γ(X,⊤) 2 ![LinearMap.proj 0,LinearMap.proj 1]))
    (exteriorPower.ιMulti Γ(X,⊤) 2 ![freeSectionCoordinates X 2 s,freeSectionCoordinates X 2 t])
  exact h1.trans (h2.trans (coordinate_pair (freeSectionCoordinates X 2 s) (freeSectionCoordinates X 2 t)))

/-- Actual wedge vanishing, transported by the actual frame map,
implies the actual determinant is zero as a ring element. -/
theorem determinant_eq_zero_of_wedge_eq_zero {F : X.Modules}
    (eF : F ≅ freeOn X 2) (s t : Γ(F,⊤))
    (h : LagrangianGrassmannian.wedgeSection X F s t = 0) :
    freeSectionCoordinates X 2 (eF.hom.app ⊤ s) 0 *
        freeSectionCoordinates X 2 (eF.hom.app ⊤ t) 1 -
      freeSectionCoordinates X 2 (eF.hom.app ⊤ s) 1 *
        freeSectionCoordinates X 2 (eF.hom.app ⊤ t) 0 = 0 := by
  have hz : LagrangianGrassmannian.wedgeSection X (freeOn X 2)
      (eF.hom.app ⊤ s) (eF.hom.app ⊤ t) = 0 := by
    rw [← LagrangianGrassmannian.exteriorPowerMap_wedgeSection, h, map_zero]
  have hh := congrArg (determinantCoordinate X) hz
  simpa only [determinantCoordinate_wedge, map_zero] using hh

/-- The same conclusion is attached to the literal selected columns of
the literal original morphism, rather than to a replacement matrix. -/
theorem selectedMatrix_det_eq_zero {F : X.Modules} (φ : freeOn X 3 ⟶ F)
    (eF : F ≅ freeOn X 2) (e : Fin 2 ↪ Fin 3)
    (h : LagrangianGrassmannian.wedgeSection X F
      (φ.app ⊤ (freeBasisSection X 3 (e 0)))
      (φ.app ⊤ (freeBasisSection X 3 (e 1))) = 0) :
    ((Stacks.FreeSheafMatrix.toMatrix (φ ≫ eF.hom)).submatrix id e).det = 0 := by
  have hh := determinant_eq_zero_of_wedge_eq_zero X eF _ _ h
  have hc (i j : Fin 2) : freeSectionCoordinates X 2
      (eF.hom.app ⊤ (φ.app ⊤ (freeBasisSection X 3 (e j)))) i =
        Stacks.FreeSheafMatrix.toMatrix (φ ≫ eF.hom) i (e j) :=
    freeCoordinates_map_basis (φ ≫ eF.hom) i (e j)
  rw [hc 0 0, hc 1 1, hc 1 0, hc 0 1] at hh
  simpa only [Matrix.det_fin_two, Matrix.submatrix_apply, id_eq, mul_comm] using hh

end M9Native.FreeTwoWedgeDeterminant
