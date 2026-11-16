module

public import M9StacksIntegration.LagrangianCommonKernelChartAlgebra
public import M9StacksIntegration.LagrangianTranslatedFiveMinorSections
public import M9StacksIntegration.SplitQuadricAffineAlgebra

/-!
# The actual original five coordinates on the four surviving charts

These are literal minors of the original inverse-swapped graph quotient
after its actual first-row/column ideal is killed. No projective-coordinate
normalization, arbitrary primitive-basis enumeration, or field-point
detection is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Matrix

universe u

namespace M9Native.LagrangianKernelTailMatrix

open LagrangianAdmissibleMinors LagrangianAdmissibleCharts LagrangianCommonKernelChartAlgebra
open LagrangianTransitivity LagrangianMatrixChart LagrangianTranslatedDeterminantSections
open LagrangianCommonKernelQuadric LagrangianPluckerFirstJet

variable (R : Type u) [CommRing R]

theorem swap_inverse_fcolumn (s : Choice) (j : Fin 3) :
    (matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹).col (Fin.natAdd 3 j) =
      if s j then Pi.single (j.castAdd 3) 1 else Pi.single (Fin.natAdd 3 j) 1 := by
  funext i
  obtain ⟨i, rfl⟩ := splitIndex.surjective i
  cases i with
  | inl i =>
    change matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹ (splitIndex (Sum.inl i))
      (splitIndex (Sum.inr j)) = _
    rw [matrixSix_apply_split, swap_inverse_matrix]
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.fromBlocks, keep, take, splitIndex, finSumFinEquiv, Pi.single_apply] <;>
      split_ifs <;> simp_all
  | inr i =>
    change matrixSix R (LagrangianAdmissibleCharts.swap R s)⁻¹ (splitIndex (Sum.inr i))
      (splitIndex (Sum.inr j)) = _
    rw [matrixSix_apply_split, swap_inverse_matrix]
    fin_cases i <;> fin_cases j
    all_goals simp [Matrix.fromBlocks, keep, take, splitIndex, finSumFinEquiv, Pi.single_apply] <;>
      split_ifs <;> simp_all

theorem product_mapped_swap_inverse_fcolumn {S : Type u} [CommRing S] (ρ : R →+* S)
    (M : Matrix (Fin 3) (Fin 6) S) (s : Choice) (j : Fin 3) :
    (M * matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col
        (Fin.natAdd 3 j) = if s j then M.col (j.castAdd 3) else M.col (Fin.natAdd 3 j) := by
  have hm : (matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col
        (Fin.natAdd 3 j) =
      if s j then Pi.single (j.castAdd 3) 1 else Pi.single (Fin.natAdd 3 j) 1 := by
    rw [matrixSix_map]
    funext i
    have h := congrArg (fun v : Fin 6 → R => ρ (v i)) (swap_inverse_fcolumn R s j)
    by_cases hs : s j <;> simpa [hs, Pi.single_apply] using h
  funext i
  change M.mulVec ((matrixSix S (mapSymplectic R ρ (LagrangianAdmissibleCharts.swap R s)⁻¹)).col
    (Fin.natAdd 3 j)) i = _
  rw [hm]
  by_cases hs : s j <;> simp [hs]

/-- The four actual tail choices in pivot order p00,q22,q11,b. -/
def choice : Fin 4 → Choice :=
  ![![true,false,false], ![true,true,false], ![true,false,true], ![true,true,true]]

theorem choice_first (c : Fin 4) : choice c 0 = true := by fin_cases c <;> rfl

variable (K : Type u) [Field K] [CharZero K]

abbrev ThreeRing := MvPolynomial (Fin 3) K

def tailMatrix (s : Choice) : Matrix (Fin 3) (Fin 6) (ThreeRing K) :=
  (translatedMatrix K (LagrangianAdmissibleCharts.swap K s)⁻¹).map (eraseHeadThree K).toRingHom

theorem erased_graphMatrix (i j : Fin 3) :
    eraseHeadThree K (MukaiConormalBigCellSections.graphMatrix K i j) =
      ![![0,0,0], ![0,MvPolynomial.X 0,MvPolynomial.X 1],
        ![0,MvPolynomial.X 1,MvPolynomial.X 2]] i j := by
  fin_cases i <;> fin_cases j
  all_goals first
    | exact eraseHeadThree_headVariable K 0
    | exact eraseHeadThree_headVariable K 1
    | exact eraseHeadThree_headVariable K 2
    | exact eraseHeadThree_tailVariable K 0
    | exact eraseHeadThree_tailVariable K 1
    | exact eraseHeadThree_tailVariable K 2

theorem tailMatrix_first (s : Choice) (i j : Fin 3) :
    tailMatrix K s i (j.castAdd 3) =
      if s j then -eraseHeadThree K (MukaiConormalBigCellSections.graphMatrix K i j)
        else (Pi.single j (1 : ThreeRing K) : Fin 3 → ThreeRing K) i := by
  have h := congrArg (fun v => eraseHeadThree K (v i))
    (product_mapped_swap_inverse_column K (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K)
      (MukaiConormalBigCellSections.graphQuotientMatrix K) s j)
  simp only [ite_apply, Matrix.col_apply, Pi.neg_apply] at h
  have he : eraseHeadThree K (MukaiConormalBigCellSections.graphQuotientMatrix K i (j.castAdd 3)) =
      (Pi.single j (1 : ThreeRing K) : Fin 3 → ThreeRing K) i := by
    rw [MukaiConormalBigCellSections.graphQuotientMatrix, standard_e]
    by_cases hij : i = j <;> simp [hij, Pi.single_apply, Ne.symm]
  have hf : eraseHeadThree K (MukaiConormalBigCellSections.graphQuotientMatrix K i (Fin.natAdd 3 j)) =
      eraseHeadThree K (MukaiConormalBigCellSections.graphMatrix K i j) :=
    congrArg (eraseHeadThree K) (standard_f (MukaiConormalBigCellSections.Ring K)
      (MukaiConormalBigCellSections.graphMatrix K) i j)
  change eraseHeadThree K ((MukaiConormalBigCellSections.graphQuotientMatrix K *
    matrixSix (MukaiConormalBigCellSections.Ring K)
      (mapSymplectic K MvPolynomial.C (LagrangianAdmissibleCharts.swap K s)⁻¹)) i (j.castAdd 3)) = _
  by_cases hs : s j
  · simp only [hs, if_true, map_neg] at h ⊢
    exact h.trans (congrArg Neg.neg hf)
  · simp only [hs, if_false] at h ⊢
    exact h.trans he

theorem tailMatrix_last (s : Choice) (i j : Fin 3) :
    tailMatrix K s i (Fin.natAdd 3 j) =
      if s j then (Pi.single j (1 : ThreeRing K) : Fin 3 → ThreeRing K) i
        else eraseHeadThree K (MukaiConormalBigCellSections.graphMatrix K i j) := by
  have h := congrArg (fun v => eraseHeadThree K (v i))
    (product_mapped_swap_inverse_fcolumn K (MvPolynomial.C : K →+* MukaiConormalBigCellSections.Ring K)
      (MukaiConormalBigCellSections.graphQuotientMatrix K) s j)
  simp only [ite_apply, Matrix.col_apply] at h
  have he : eraseHeadThree K (MukaiConormalBigCellSections.graphQuotientMatrix K i (j.castAdd 3)) =
      (Pi.single j (1 : ThreeRing K) : Fin 3 → ThreeRing K) i := by
    rw [MukaiConormalBigCellSections.graphQuotientMatrix, standard_e]
    by_cases hij : i = j <;> simp [hij, Pi.single_apply, Ne.symm]
  have hf : eraseHeadThree K (MukaiConormalBigCellSections.graphQuotientMatrix K i (Fin.natAdd 3 j)) =
      eraseHeadThree K (MukaiConormalBigCellSections.graphMatrix K i j) :=
    congrArg (eraseHeadThree K) (standard_f (MukaiConormalBigCellSections.Ring K)
      (MukaiConormalBigCellSections.graphMatrix K) i j)
  change eraseHeadThree K ((MukaiConormalBigCellSections.graphQuotientMatrix K *
    matrixSix (MukaiConormalBigCellSections.Ring K)
      (mapSymplectic K MvPolynomial.C (LagrangianAdmissibleCharts.swap K s)⁻¹)) i (Fin.natAdd 3 j)) = _
  by_cases hs : s j
  · simp only [hs, if_true] at h ⊢
    exact h.trans he
  · simp only [hs, if_false] at h ⊢
    exact h.trans hf

def matrixFormula : Fin 4 → Matrix (Fin 3) (Fin 6) (ThreeRing K) :=
  ![![![0,0,0,1,0,0], ![0,1,0,0,MvPolynomial.X 0,MvPolynomial.X 1],
        ![0,0,1,0,MvPolynomial.X 1,MvPolynomial.X 2]],
    ![![0,0,0,1,0,0], ![0,-MvPolynomial.X 0,0,0,1,MvPolynomial.X 1],
        ![0,-MvPolynomial.X 1,1,0,0,MvPolynomial.X 2]],
    ![![0,0,0,1,0,0], ![0,1,-MvPolynomial.X 1,0,MvPolynomial.X 0,0],
        ![0,0,-MvPolynomial.X 2,0,MvPolynomial.X 1,1]],
    ![![0,0,0,1,0,0], ![0,-MvPolynomial.X 0,-MvPolynomial.X 1,0,1,0],
        ![0,-MvPolynomial.X 1,-MvPolynomial.X 2,0,0,1]]]

theorem tailMatrix_formula (c : Fin 4) : tailMatrix K (choice c) = matrixFormula K c := by
  ext i j
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · rw [tailMatrix_first, erased_graphMatrix]
    fin_cases c <;> fin_cases i <;> fin_cases j <;> simp [choice, matrixFormula, Pi.single_apply]
  · rw [tailMatrix_last, erased_graphMatrix]
    fin_cases c <;> fin_cases i <;> fin_cases j <;> simp [choice, matrixFormula, Pi.single_apply]

def fiveFormula : Fin 4 → Fin 5 → ThreeRing K :=
  ![![MvPolynomial.X 2,-MvPolynomial.X 1,MvPolynomial.X 0,1,
        MvPolynomial.X 0 * MvPolynomial.X 2 - (MvPolynomial.X 1)^2],
    ![-MvPolynomial.X 0 * MvPolynomial.X 2 + (MvPolynomial.X 1)^2,
        -MvPolynomial.X 1,1,-MvPolynomial.X 0,MvPolynomial.X 2],
    ![1,-MvPolynomial.X 1,-MvPolynomial.X 0 * MvPolynomial.X 2 + (MvPolynomial.X 1)^2,
        -MvPolynomial.X 2,MvPolynomial.X 0],
    ![-MvPolynomial.X 0,-MvPolynomial.X 1,-MvPolynomial.X 2,
        MvPolynomial.X 0 * MvPolynomial.X 2 - (MvPolynomial.X 1)^2,1]]

/-- Literal original maximal minors; every sign comes from the actual inverse swap. -/
theorem tailFive_formula (c : Fin 4) :
    fiveCoordinates (ThreeRing K) (tailMatrix K (choice c)) = fiveFormula K c := by
  rw [tailMatrix_formula]
  funext a
  fin_cases c <;> fin_cases a <;>
    norm_num [fiveCoordinates, orderedMinor, matrixFormula, fiveFormula, Matrix.det_fin_three,
      Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, id_eq] <;> ring

theorem fiveFormula_pivot (c : Fin 4) : fiveFormula K c (SplitQuadricAffineAlgebra.pivot c) = 1 := by
  fin_cases c <;> rfl

end M9Native.LagrangianKernelTailMatrix
