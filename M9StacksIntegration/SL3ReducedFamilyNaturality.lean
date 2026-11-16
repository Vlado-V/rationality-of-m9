module

public import M9StacksIntegration.SL3ReducedFamily
public import Mathlib.LinearAlgebra.Matrix.Dual

@[expose] public section

/-! Actual coordinate formulas for the uniform reduced family. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open Matrix Module

namespace M9Native.SL3ReducedFamilyNaturality

open SL3ReducedFamily

def coordinateIndex : (M9.Upper3 ⊕ M9.Upper3) ≃ Fin 12 :=
  (((Equiv.sumCongr M9.GraphBundleDescent.upperSplitIndex M9.GraphBundleDescent.upperSplitIndex).trans
    (Equiv.sumAssoc (Fin 4) (Fin 2) (Fin 4 ⊕ Fin 2))).trans
      (Equiv.sumCongr (Equiv.refl (Fin 4)) GraphGrassmannianChart.rowEquiv)).trans finSumFinEquiv

variable (R : Type) [CommRing R]

def dualCoordinates : Module.Dual R (UpperSpace R) ≃ₗ[R] UpperSpace R :=
  (Pi.basisFun R M9.Upper3).dualBasis.equivFun

theorem dualCoordinates_apply (α : Module.Dual R (UpperSpace R)) (i : M9.Upper3) :
    dualCoordinates R α i = α (Pi.single i 1) := by
  simpa only [dualCoordinates, Pi.basisFun_apply] using
    (Pi.basisFun R M9.Upper3).dualBasis_equivFun α i

theorem split_symm_basis (j : Fin 4 ⊕ Fin 2) :
    (split R).symm (splitBasis R j) = Pi.single (M9.GraphBundleDescent.upperSplitIndex.symm j) 1 := by
  change (LinearEquiv.funCongrLeft R R M9.GraphBundleDescent.upperSplitIndex.symm).symm
    ((LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R).symm
      ((Pi.basisFun R (Fin 4 ⊕ Fin 2)).map
        (LinearEquiv.sumArrowLequivProdArrow (Fin 4) (Fin 2) R R) j)) = _
  rw [Basis.map_apply, LinearEquiv.symm_apply_apply, Pi.basisFun_apply]
  funext i
  change (Pi.single j (1 : R) : (Fin 4 ⊕ Fin 2) → R)
      (M9.GraphBundleDescent.upperSplitIndex i) =
    (Pi.single (M9.GraphBundleDescent.upperSplitIndex.symm j) (1 : R) : M9.Upper3 → R) i
  by_cases hi : i = M9.GraphBundleDescent.upperSplitIndex.symm j
  · subst i
    simp
  · have hu : M9.GraphBundleDescent.upperSplitIndex i ≠ j := by
      intro h
      exact hi (by rw [← M9.GraphBundleDescent.upperSplitIndex.symm_apply_apply i, h])
    simp [hi, hu]

theorem coordinates_inl (z : Mixed R) (i : M9.Upper3) :
    coordinates R z (coordinateIndex (Sum.inl i)) = z.1 i := by
  obtain ⟨j, rfl⟩ := M9.GraphBundleDescent.upperSplitIndex.symm.surjective i
  cases j <;> simp [coordinates, coordinateIndex, GraphGrassmannianChart.ambientCoordinates_apply,
    split]

theorem coordinates_inr (z : Mixed R) (i : M9.Upper3) :
    coordinates R z (coordinateIndex (Sum.inr i)) = dualCoordinates R z.2 i := by
  obtain ⟨j, rfl⟩ := M9.GraphBundleDescent.upperSplitIndex.symm.surjective i
  have he : coordinates R z
      (coordinateIndex (Sum.inr (M9.GraphBundleDescent.upperSplitIndex.symm j))) =
      (splitBasis R).dualBasis.equivFun ((split R).dualMap.symm z.2) j := by
    cases j <;> simp [coordinates, coordinateIndex, GraphGrassmannianChart.ambientCoordinates_apply,
      dualSplit]
  rw [he, Basis.dualBasis_equivFun, dualCoordinates_apply]
  change z.2 ((split R).symm (splitBasis R j)) = _
  rw [split_symm_basis]

/-- The actual dual-basis action is the transpose of the original matrix. -/
theorem dualCoordinates_dualMap (f : UpperSpace R →ₗ[R] UpperSpace R)
    (α : Module.Dual R (UpperSpace R)) :
    dualCoordinates R (f.dualMap α) = (LinearMap.toMatrix' f).transpose *ᵥ dualCoordinates R α := by
  have h := LinearMap.toMatrix_mulVec_repr
    (Pi.basisFun R M9.Upper3).dualBasis (Pi.basisFun R M9.Upper3).dualBasis f.dualMap α
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose, LinearMap.toMatrix_eq_toMatrix'] at h
  exact h.symm

theorem coordinates_comp_index (z : Mixed R) :
    coordinates R z ∘ coordinateIndex = Sum.elim z.1 (dualCoordinates R z.2) := by
  funext i
  cases i with
  | inl i => exact coordinates_inl R z i
  | inr i => exact coordinates_inr R z i

def blockMatrix (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    Matrix (M9.Upper3 ⊕ M9.Upper3) (M9.Upper3 ⊕ M9.Upper3) R :=
  Matrix.fromBlocks (SL3SymmetricCoordinates.matrix R g.val) 0 0
    (SL3SymmetricCoordinates.matrix R (g⁻¹).val).transpose

theorem mixed_action_block (g : Matrix.SpecialLinearGroup (Fin 3) R) (z : Mixed R) :
    coordinates R (mixedLinearEquiv R g z) ∘ coordinateIndex =
      blockMatrix R g *ᵥ (coordinates R z ∘ coordinateIndex) := by
  rw [coordinates_comp_index, coordinates_comp_index, blockMatrix, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, zero_add]
  apply congrArg₂ Sum.elim
  · exact (SL3SymmetricCoordinates.matrix_mulVec R g.val z.1).symm
  · exact dualCoordinates_dualMap R (SL3SymmetricCoordinates.linearEquiv R g⁻¹).toLinearMap z.2

/-- The actual family has the literal polynomial congruence block and
the transpose inverse on its genuine dual. -/
theorem matrixGL_block (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (matrixGL R g).val =
      (blockMatrix R g).submatrix coordinateIndex.symm coordinateIndex.symm := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  obtain ⟨z, rfl⟩ := (coordinates R).surjective v
  change (matrixGL R g).val *ᵥ coordinates R z =
    (blockMatrix R g).submatrix coordinateIndex.symm coordinateIndex.symm *ᵥ coordinates R z
  rw [matrixGL_mulVec, Matrix.submatrix_mulVec_equiv]
  change coordinates R (mixedLinearEquiv R g ((coordinates R).symm (coordinates R z))) = _
  rw [LinearEquiv.symm_apply_apply]
  funext k
  obtain ⟨i, rfl⟩ := coordinateIndex.surjective k
  simpa only [Function.comp_apply, Equiv.symm_apply_apply, Equiv.symm_symm] using
    congrFun (mixed_action_block R g z) i

variable {S : Type} [CommRing S]

theorem blockMatrix_map (ρ : R →+* S) (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (blockMatrix R g).map ρ = blockMatrix S (Matrix.SpecialLinearGroup.map ρ g) := by
  have hi : ((Matrix.SpecialLinearGroup.map ρ g)⁻¹).val = (g⁻¹).val.map ρ :=
    congrArg Subtype.val ((Matrix.SpecialLinearGroup.map ρ).map_inv g).symm
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      exact congrFun (congrFun (SL3SymmetricCoordinates.matrix_map R ρ g.val) i) j
    | inr j => exact map_zero ρ
  | inr i =>
    cases j with
    | inl j => exact map_zero ρ
    | inr j =>
      change ρ (SL3SymmetricCoordinates.matrix R (g⁻¹).val j i) =
        SL3SymmetricCoordinates.matrix S ((Matrix.SpecialLinearGroup.map ρ g)⁻¹).val j i
      rw [hi]
      exact congrFun (congrFun (SL3SymmetricCoordinates.matrix_map R ρ (g⁻¹).val) j) i

/-- Every ring specialization of the actual twelve-coordinate family is
the same actual family of the specialized special-linear matrix. -/
theorem matrixGL_map (ρ : R →+* S) (g : Matrix.SpecialLinearGroup (Fin 3) R) :
    (matrixGL R g).val.map ρ = (matrixGL S (Matrix.SpecialLinearGroup.map ρ g)).val := by
  rw [matrixGL_block, matrixGL_block]
  ext i j
  exact congrFun (congrFun (blockMatrix_map R ρ g) (coordinateIndex.symm i)) (coordinateIndex.symm j)

end M9Native.SL3ReducedFamilyNaturality
