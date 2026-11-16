module

public import M9StacksIntegration.LagrangianGraphSpan
public import M9StacksIntegration.MukaiConormalBigCellFirstJet
public import M9StacksIntegration.LagrangianHyperplaneCoordinates

/-! Independence of the original fourteen actual LG determinant
sections, proved on the genuine native affine symmetric-matrix chart. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Module Matrix
open scoped BigOperators

universe u

namespace M9Native.LagrangianPrimitiveIndependence

open LagrangianField LagrangianPluckerFirstJet LagrangianMatrixChart
open LagrangianPluckerQuotient MukaiConormalBigCellSections

variable (K : Type u) [Field K] [CharZero K]

abbrev PolynomialRing := MukaiConormalBigCellSections.Ring K

/-- Evaluation of the actual six original chart variables at a literal
symmetric matrix, respecting the frozen upper-entry enumeration. -/
def graphEval (A : Symmetric3 K) : PolynomialRing K →ₐ[K] K :=
  MvPolynomial.aeval (fun i : Fin 6 =>
    A.val (symmetricEntryEquivFinSix.{u}.symm i).down.val.1
      (symmetricEntryEquivFinSix.{u}.symm i).down.val.2)

omit [CharZero K] in
theorem graphMatrix_eval (A : Symmetric3 K) :
    (graphMatrix K).map (graphEval K A).toRingHom = A.val := by
  ext i j
  change graphEval K A (MvPolynomial.X
    (symmetricEntryEquivFinSix (ULift.up.{u} (symmetricIndex (i,j))))) = _
  rw [graphEval, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  change A.val (symmetricIndex (i,j)).val.1 (symmetricIndex (i,j)).val.2 = A.val i j
  by_cases h : i ≤ j
  · simp [symmetricIndex,h]
  · simpa [symmetricIndex,h] using congrFun (congrFun A.property i) j

omit [CharZero K] in
theorem graphQuotient_eval (A : Symmetric3 K) :
    (graphQuotientMatrix K).map (graphEval K A).toRingHom = standard K A.val := by
  rw [graphQuotientMatrix, MukaiConormalBigCellFirstJet.standard_map,graphMatrix_eval]

omit [CharZero K] in
theorem rowFourteen_graph (A : Symmetric3 K) (j : Fin 14) :
    LagrangianRing.rowFourteen K (RingHom.id K) (standard K A.val) j =
      (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) j := by
  rw [LagrangianRing.rowFourteen_id_eq_field]
  unfold LagrangianField.rowFourteen
  have hrow : LagrangianField.rowPlucker K (standard K A.val) =
      LagrangianRing.rowPlucker K (standard K A.val) := by
    unfold LagrangianRing.rowPlucker LagrangianField.rowPlucker LagrangianField.wedge3
    congr 1
  rw [hrow,coordinateProjection_standard]
  rfl

omit [CharZero K] in
theorem sectionPolynomial_graphEval (A : Symmetric3 K) (j : Fin 14) :
    graphEval K A (sectionPolynomial K j) =
      (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) j := by
  have hc : (graphEval K A).toRingHom.comp (MvPolynomial.C : K →+* PolynomialRing K) =
      RingHom.id K := by
    ext a
    exact (graphEval K A).commutes a
  have h := congrFun (LagrangianPlucker.rowFourteen_map K
    (MvPolynomial.C : K →+* PolynomialRing K) (graphEval K A).toRingHom
      (graphQuotientMatrix K)) j
  rw [hc,graphQuotient_eval] at h
  exact h.symm.trans (rowFourteen_graph K A j)

def polynomialCombination (v : Fin 14 → K) : PolynomialRing K :=
  ∑ i : Fin 14, MvPolynomial.C (v i) * sectionPolynomial K i

omit [CharZero K] in
theorem polynomialCombination_graphEval (A : Symmetric3 K) (v : Fin 14 → K) :
    graphEval K A (polynomialCombination K v) =
      ∑ i : Fin 14, v i *
        (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) i := by
  simp only [polynomialCombination,map_sum,map_mul,sectionPolynomial_graphEval]
  apply Finset.sum_congr rfl
  intro i _
  rw [show graphEval K A (MvPolynomial.C (v i)) = v i from (graphEval K A).commutes _]

theorem coefficients_eq_zero_of_polynomialCombination (v : Fin 14 → K)
    (hv : polynomialCombination K v = 0) : v = 0 := by
  apply LagrangianGraphSpan.coefficients_eq_zero_of_graph K v
  intro A
  rw [← polynomialCombination_graphEval,hv,map_zero]

omit [CharZero K] in
theorem rootCoefficient_comp {T : Scheme.{u}} (g : T ⟶ LagrangianGrassmannian.space K)
    (a : K) :
    g.appTop.hom (LagrangianHyperplaneCoordinates.coefficientMap K a) =
      LagrangianPlucker.coefficientMap K g a := by
  have hc : g.appTop.hom.comp (LagrangianHyperplaneCoordinates.coefficientMap K) =
      LagrangianPlucker.coefficientMap K g := by
    simpa only [Category.comp_id,LagrangianHyperplaneCoordinates.coefficientMap] using
      (LagrangianPlucker.coefficientMap_comp K (𝟙 _) g).symm
  exact RingHom.congr_fun hc a

omit [CharZero K] in
theorem bigCell_rootCoefficient (a : K) :
    (bigCell K).appTop.hom (LagrangianHyperplaneCoordinates.coefficientMap K a) =
      scalarEquiv K (MvPolynomial.C a) :=
  (rootCoefficient_comp K (bigCell K) a).trans
    (RingHom.congr_fun (bigCell_coefficientMap K) a)

omit [CharZero K] in
/-- The literal original determinant section becomes the corresponding
literal polynomial combination in the actual native quotient frame. -/
theorem determinantIso_linearSection (v : Fin 14 → K) :
    (determinantIso K).hom.app ⊤
      (pullbackGlobalSections (bigCell K) (determinantLine K)
        (LagrangianHyperplaneCoordinates.determinantSection K v)) =
      scalarEquiv K (polynomialCombination K v) := by
  let E : Γ((Scheme.Modules.pullback (bigCell K)).obj (determinantLine K),⊤) →ₗ[Γ(chart K,⊤)]
      Γ(chart K,⊤) := {
    toFun := (determinantIso K).hom.app ⊤
    map_add' := fun s t => ((determinantIso K).hom.app ⊤).hom.map_add s t
    map_smul' := fun a s => Scheme.Modules.Hom.app_smul (determinantIso K).hom a s }
  have he (i : Fin 14) :
      E (pullbackGlobalSections (bigCell K) (determinantLine K) (primitiveSections K i)) =
        scalarEquiv K (sectionPolynomial K i) := determinantIso_coordinate K i
  change E (pullbackGlobalSections (bigCell K) (determinantLine K)
    (LagrangianHyperplaneCoordinates.determinantSection K v)) = _
  have hsum : scalarEquiv K (polynomialCombination K v) =
      ∑ i : Fin 14, scalarEquiv K (MvPolynomial.C (v i) * sectionPolynomial K i) :=
    map_sum (scalarEquiv K).toRingHom _ _
  rw [hsum]
  simp only [LagrangianHyperplaneCoordinates.determinantSection,map_sum,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    map_smul,he]
  apply Finset.sum_congr rfl
  intro i _
  rw [bigCell_rootCoefficient]
  change scalarEquiv K (MvPolynomial.C (v i)) * scalarEquiv K (sectionPolynomial K i) = _
  exact ((scalarEquiv K).map_mul _ _).symm

/-- Independence of the original fourteen sections on the actual LG,
with its original structural coefficient map. -/
theorem coefficients_eq_zero_of_determinantSection (v : Fin 14 → K)
    (hv : LagrangianHyperplaneCoordinates.determinantSection K v = 0) : v = 0 := by
  apply coefficients_eq_zero_of_polynomialCombination K v
  apply (scalarEquiv K).injective
  have h := congrArg (fun t : Γ(determinantLine K,⊤) =>
    (determinantIso K).hom.app ⊤ (pullbackGlobalSections (bigCell K) (determinantLine K) t)) hv
  rw [determinantIso_linearSection,map_zero,map_zero] at h
  exact h.trans ((scalarEquiv K).map_zero).symm

end M9Native.LagrangianPrimitiveIndependence
end
