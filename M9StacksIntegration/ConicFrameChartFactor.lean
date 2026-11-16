module

public import M9StacksIntegration.GrassmannianChartClass

/-! The actual polynomial quotient family factors through its genuine
native matrix chart wherever its selected quotient minor is a unit. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.ConicFrameChartFactor

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix M9Native.ConicFrame

variable (T : Scheme.{u}) (ι : Fin 2 ↪ Fin 6)

def normalizedMatrix (Q : Matrix (Fin 2) (Fin 6) Γ(T, ⊤)) :
    Matrix (Fin 2) (Fin 6) Γ(T, ⊤) :=
  (Q.submatrix id ι)⁻¹ * Q

theorem normalizedMatrix_pivots (Q : Matrix (Fin 2) (Fin 6) Γ(T, ⊤))
    (hQ : IsUnit (Q.submatrix id ι).det) :
    (normalizedMatrix T ι Q).submatrix id ι = 1 := by
  rw [normalizedMatrix,Matrix.submatrix_mul _ _ id id ι Function.bijective_id,
    Matrix.submatrix_id_id,Matrix.nonsing_inv_mul _ hQ]

def coefficientMap (E : Matrix (Fin 2) (Fin 6) Γ(T, ⊤)) :
    T ⟶ coordinateChartScheme.{u} (k := 4) (n := 6) ι :=
  (AffineSpace.toSpecMvPolyIntEquiv (ChartIndex.{u} (k := 4) (n := 6) ι)).symm
    (fun a => E a.down.2 a.down.1.val)

theorem coefficientMap_matrix (E : Matrix (Fin 2) (Fin 6) Γ(T, ⊤))
    (hE : E.submatrix id ι = 1) :
    toMatrix (chartQuotientMap 4 6 ι (coefficientMap T ι E)) = E := by
  rw [toMatrix_chartQuotientMap]
  classical
  ext i j
  by_cases hj : j ∈ Set.range ι
  · obtain ⟨j',rfl⟩ := hj
    rw [chartMatrix_apply_self]
    have hh := congrFun (congrFun hE i) j'
    change E i (ι j') = (1 : Matrix (Fin 2) (Fin 2) Γ(T, ⊤)) i j' at hh
    simp only [hh,Matrix.one_apply]
  · rw [chartMatrix_apply_of_notMem ι _ i hj]
    simp only [coefficientMap,Equiv.apply_symm_apply]

def matrixIso (A : Matrix (Fin 2) (Fin 2) Γ(T, ⊤)) (hA : IsUnit A.det) :
    Stacks.FreeSheafMatrix.F T 2 ≅ Stacks.FreeSheafMatrix.F T 2 where
  hom := ofMatrix A
  inv := ofMatrix A⁻¹
  hom_inv_id := by
    apply toMatrix_injective
    rw [toMatrix_comp,toMatrix_ofMatrix,toMatrix_ofMatrix,toMatrix_id,
      Matrix.nonsing_inv_mul _ hA]
  inv_hom_id := by
    apply toMatrix_injective
    rw [toMatrix_comp,toMatrix_ofMatrix,toMatrix_ofMatrix,toMatrix_id,
      Matrix.mul_nonsing_inv _ hA]

/-- Normalizing the quotient matrix changes only its actual target bundle basis. -/
theorem presentation_isomorphic (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (hQ : IsUnit ((quotientMatrix F).submatrix id ι).det) :
    (ConicFrame.presentation T F hF).Isomorphic
      (normalizedQuotientPresentation T 4 6 ι
        (GrassmannianChartClass.normalized 4 6 ι
          (coefficientMap T ι (normalizedMatrix T ι (quotientMatrix F))))) := by
  let P := (quotientMatrix F).submatrix id ι
  refine ⟨matrixIso T P⁻¹ (Matrix.isUnit_nonsing_inv_det _ hQ),?_⟩
  change sheafQuotient T F ≫ (matrixIso T P⁻¹ _).hom =
    (GrassmannianChartClass.normalized 4 6 ι
      (coefficientMap T ι (normalizedMatrix T ι (quotientMatrix F)))).val
  rw [GrassmannianChartClass.normalized_map]
  apply toMatrix_injective
  rw [toMatrix_comp,coefficientMap_matrix T ι _ (normalizedMatrix_pivots T ι _ hQ)]
  simp only [sheafQuotient,matrixIso,toMatrix_ofMatrix,normalizedMatrix,P]

/-- This is an equality of the actual classifying morphisms into the native scheme. -/
theorem integralMap_eq_chart (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (hQ : IsUnit ((quotientMatrix F).submatrix id ι).det) :
    ConicFrame.integralMap T F hF =
      coefficientMap T ι (normalizedMatrix T ι (quotientMatrix F)) ≫ chart 4 6 ι := by
  apply (schemeRepresentableBy 4 6).homEquiv.injective
  apply ((functorData 4 6).objEquiv T).injective
  rw [ConicFrame.integralMap_class,GrassmannianChartClass.chart_class]
  exact Quotient.sound (.rel _ _ (presentation_isomorphic T ι F hF hQ))

variable (K : Type u) [Field K]

/-- The genuinely base-changed coordinate-chart factor. -/
def affineFactor (p : T ⟶ Spec (.of K)) (E : Matrix (Fin 2) (Fin 6) Γ(T, ⊤)) :
    T ⟶ GrassmannianCharts.chartSpace K 4 6 ι :=
  pullback.lift p (coefficientMap T ι E) (terminal.hom_ext _ _)

theorem map_eq_chartOver (p : T ⟶ Spec (.of K))
    (F : Mat3 Γ(T, ⊤)) (hF : IsUnit F.det)
    (hQ : IsUnit ((quotientMatrix F).submatrix id ι).det) :
    ConicFrame.map T K p F hF =
      affineFactor T ι K p (normalizedMatrix T ι (quotientMatrix F)) ≫
        GrassmannianCharts.chartOver K 4 6 ι := by
  apply pullback.hom_ext
  · simp only [ConicFrame.map_projection,Category.assoc,GrassmannianCharts.chartOver_projection,
      affineFactor,pullback.lift_fst]
  · rw [ConicFrame.map_toIntegral,Category.assoc,GrassmannianCharts.chartOver_toIntegral,
      ← Category.assoc]
    simp only [affineFactor,pullback.lift_snd]
    exact integralMap_eq_chart T ι F hF hQ

end M9Native.ConicFrameChartFactor
