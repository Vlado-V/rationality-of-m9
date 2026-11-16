module

public import M9StacksIntegration.Sp6GaussCellFunctor
public import M9StacksIntegration.LagrangianIntegral

/-!
# The eight actual Gauss minors of a symplectic matrix

The literal top three rows are a surjective isotropic quotient over
every commutative ring. The frozen admissible-minor theorem therefore
puts every field-valued symplectic matrix into one of the eight true
Gauss cells after the corresponding actual signed column swap.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

open Matrix

universe u

namespace M9Native.Sp6AdmissibleCellMatrices

open LagrangianTransitivity LagrangianMatrixChart
open LagrangianAdmissibleMinors LagrangianAdmissibleCharts

variable {R : Type u} [CommRing R]

def topRows (g : Matrix.symplecticGroup (Fin 3) R) : Matrix (Fin 3) (Fin 6) R :=
  (matrixSix R g).submatrix firstPivot id

theorem topRows_first (g : Matrix.symplecticGroup (Fin 3) R) (i j : Fin 3) :
    topRows g i (j.castAdd 3) = g.val.toBlocks₁₁ i j := by
  change matrixSix R g (splitIndex (Sum.inl i)) (splitIndex (Sum.inl j)) = _
  exact matrixSix_apply_split R g (Sum.inl i) (Sum.inl j)

theorem topRows_last (g : Matrix.symplecticGroup (Fin 3) R) (i j : Fin 3) :
    topRows g i (Fin.natAdd 3 j) = g.val.toBlocks₁₂ i j := by
  change matrixSix R g (splitIndex (Sum.inl i)) (splitIndex (Sum.inr j)) = _
  exact matrixSix_apply_split R g (Sum.inl i) (Sum.inr j)

theorem topRows_rightInverse (g : Matrix.symplecticGroup (Fin 3) R) :
    topRows g * (matrixSix R g⁻¹).submatrix id firstPivot = 1 := by
  calc
    _ = (matrixSix R g * matrixSix R g⁻¹).submatrix firstPivot firstPivot := by
      ext i j
      rfl
    _ = 1 := by
      rw [← PrimitiveRingRepresentation.matrixSix_mul, mul_inv_cancel,
        PrimitiveRingRepresentation.matrixSix_one]
      ext i j
      simp only [Matrix.submatrix_apply, Matrix.one_apply, firstPivot.injective.eq_iff]

theorem topRows_surjective (g : Matrix.symplecticGroup (Fin 3) R) :
    Function.Surjective (topRows g).mulVec :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mpr
    ⟨(matrixSix R g⁻¹).submatrix id firstPivot,topRows_rightInverse g⟩

theorem topRows_isotropic (g : Matrix.symplecticGroup (Fin 3) R) (i j : Fin 3) :
    LagrangianRing.omega R (topRows g i) (topRows g j) = 0 := by
  have ht := SymplecticGroup.transpose_mem (Sp6GaussCellFunctor.blocks_mem g)
  rw [Matrix.fromBlocks_transpose] at ht
  have hAB : g.val.toBlocks₁₁ * g.val.toBlocks₁₂.transpose =
      g.val.toBlocks₁₂ * g.val.toBlocks₁₁.transpose := by
    simpa only [Matrix.transpose_transpose] using
      (SymplecticGroup.fromBlocks_mem_iff.mp ht).1
  have hij := congrFun (congrFun hAB i) j
  change (∑ k : Fin 3, (topRows g i (k.castAdd 3) * topRows g j (Fin.natAdd 3 k) -
    topRows g i (Fin.natAdd 3 k) * topRows g j (k.castAdd 3))) = 0
  simp only [topRows_first, topRows_last, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr (by simpa only [Matrix.mul_apply, Matrix.transpose_apply] using hij)

theorem topRows_mul_swap (g : Matrix.symplecticGroup (Fin 3) R) (s : Choice) :
    topRows (g * LagrangianAdmissibleCharts.swap R s) =
      topRows g * matrixSix R (LagrangianAdmissibleCharts.swap R s) := by
  ext i j
  change matrixSix R (g * LagrangianAdmissibleCharts.swap R s) (firstPivot i) j = _
  rw [PrimitiveRingRepresentation.matrixSix_mul]
  rfl

theorem determinant_mul_swap (g : Matrix.symplecticGroup (Fin 3) R) (s : Choice) :
    (g * LagrangianAdmissibleCharts.swap R s).val.toBlocks₁₁.det =
      admissibleMinor (topRows g) s := by
  have htop : (g * LagrangianAdmissibleCharts.swap R s).val.toBlocks₁₁ =
      (topRows (g * LagrangianAdmissibleCharts.swap R s)).submatrix id firstPivot := by
    ext i j
    exact (topRows_first (g * LagrangianAdmissibleCharts.swap R s) i j).symm
  rw [htop, topRows_mul_swap, mul_swap_firstColumns]
  rfl

theorem exists_unit_topLeft_after_swap {K : Type u} [Field K]
    (g : Matrix.symplecticGroup (Fin 3) K) :
    ∃ s : Choice, IsUnit (g * LagrangianAdmissibleCharts.swap K s).val.toBlocks₁₁.det := by
  obtain ⟨s,hs⟩ := exists_isUnit_admissibleMinor (topRows g)
    (topRows_surjective g) (topRows_isotropic g)
  exact ⟨s, (determinant_mul_swap g s).symm ▸ hs⟩

/-- The same literal upper-identity shear supplies a common point
of all eight actual Gauss cells. -/
def commonMatrix (R : Type u) [CommRing R] : Matrix.symplecticGroup (Fin 3) R :=
  PrimitiveGaussFamily.upper (1 : Matrix (Fin 3) (Fin 3) R) Matrix.transpose_one

theorem commonMatrix_topRows (R : Type u) [CommRing R] :
    topRows (commonMatrix R) = LagrangianIntegral.graphMatrix R := by
  ext i j
  obtain ⟨j,rfl⟩ := splitIndex.surjective j
  cases j with
  | inl j =>
    change topRows (commonMatrix R) i (j.castAdd 3) = _
    rw [topRows_first]
    exact (LagrangianIntegral.graphMatrix_first R i j).symm
  | inr j =>
    change topRows (commonMatrix R) i (Fin.natAdd 3 j) = _
    rw [topRows_last]
    exact (LagrangianIntegral.graphMatrix_last R i j).symm

theorem commonMatrix_unit_all (R : Type u) [CommRing R] (s : Choice) :
    IsUnit (commonMatrix R * LagrangianAdmissibleCharts.swap R s).val.toBlocks₁₁.det := by
  rw [determinant_mul_swap, commonMatrix_topRows,
    LagrangianIntegral.graphMatrix_admissibleMinor]
  exact isUnit_one

end M9Native.Sp6AdmissibleCellMatrices

