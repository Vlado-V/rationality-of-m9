module

public import M9StacksIntegration.LagrangianPolynomialPluckerEquivariance
public import M9StacksIntegration.LagrangianAdmissibleCoordinateIndices
public import M9StacksIntegration.LagrangianQuadricChartReindex
public import M9StacksIntegration.LagrangianGraphSpan
public import M9StacksIntegration.LagrangianPrimitiveRowAction
public import M9StacksIntegration.LagrangianBlockMinorQuadrics
public import M9StacksIntegration.LagrangianAdmissibleCharts

/-! The literal eight admissible coordinates are the native pullbacks of
the original a-coordinate under the actual coordinate swaps. The proof
identifies the entire coefficient row using finite graph identities;
no point-density or geometric equivariance premise is used. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open Matrix Module MvPolynomial
open scoped BigOperators

universe u

namespace M9Native.LagrangianAdmissibleSwapCoordinate

open LagrangianField LagrangianPluckerFirstJet LagrangianCoordinateBasisEntries
open LagrangianAdmissibleMinors LagrangianAdmissibleCharts LagrangianTransitivity
open LagrangianAdmissibleCoordinateIndices LagrangianQuadricChartReindex
open LagrangianPolynomialPluckerEquivariance

variable (K : Type u) [Field K]

theorem rowFourteen_projection (M : Matrix (Fin 3) (Fin 6) K) :
    LagrangianRing.rowFourteen K (RingHom.id K) M =
      (coordinateBasis14 K).equivFun (coordinateProjection K (LagrangianRing.rowPlucker K M)) := by
  change projectionMatrix K *ᵥ (LagrangianRing.thirdBasis20 K).repr
    (LagrangianRing.rowPlucker K M) = _
  rw [LagrangianRing.thirdBasis20_eq_field]
  exact LinearMap.toMatrix_mulVec_repr _ _ _ _

theorem rowFourteen_graph (A : Symmetric3 K) :
    LagrangianRing.rowFourteen K (RingHom.id K) (standard K A.val) =
      (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) := by
  rw [rowFourteen_projection,coordinateProjection_standard K ⟨A.val,A.property⟩]
  rfl

theorem rowFourteen_a (M : Matrix (Fin 3) (Fin 6) K) :
    LagrangianRing.rowFourteen K (RingHom.id K) M aIndex =
      (M.submatrix id LagrangianMatrixChart.firstPivot).det := by
  rw [rowFourteen_projection]
  change (coordinateBasis14 K).equivFun (coordinateProjection K (LagrangianRing.rowPlucker K M))
    (indexEquiv (Sum.inl ())) = _
  rw [coordinateBasis14_projection]
  change LagrangianPluckerFirstJet.aCoordinate K (LagrangianRing.rowPlucker K M) = _
  exact LagrangianBlockMinorQuadrics.aMinor_eq K M

private theorem standard_rows_isotropic (A : Symmetric3 K) (i j : Fin 3) :
    LagrangianRing.omega K (standard K A.val i) (standard K A.val j) = 0 := by
  have h : LagrangianRing.omega K (standard K A.val i) (standard K A.val j) =
      A.val j i - A.val i j := by
    fin_cases i <;> fin_cases j <;>
      simp [LagrangianRing.omegaValue,LagrangianRing.omega_apply,LagrangianRing.eIndex,LagrangianRing.fIndex,standard,Fin.sum_univ_succ]
  rw [h]
  exact sub_eq_zero.mpr (congrFun (congrFun A.property i) j)

/-- The eight actual column determinants have the exact original
(a,b,p-diagonal,q-diagonal) primitive indices. -/
theorem graph_choice_minor (A : Symmetric3 K) (s : Choice) :
    (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) (choiceIndex s) =
      ((standard K A.val).submatrix id (embedding s)).det := by
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2
  all_goals
    simp only [choiceIndex,choiceAdmissible,h0,h1,h2,
      Bool.false_eq_true,ite_true,ite_false,admissibleIndex]
    rw [Basis.equivFun_apply,coordinateBasis14_repr]
    simp [blockValue,LagrangianGraphSpan.graph,graphPoint,standard,embedding,column,
      Matrix.submatrix_apply,Matrix.det_fin_three,Matrix.adjugate_fin_three,h0,h1,h2]

variable [CharZero K]

/-- This is an equality of the whole actual raw coefficient row,
proved from the literal graph span and true swapped first columns. -/
theorem swap_a_row (s : Choice) :
    (primitiveGL K (swap K s)).val aIndex = (Pi.single (choiceIndex s) (1 : K) : Fin 14 → K) := by
  have hz : (fun j => (primitiveGL K (swap K s)).val aIndex j -
      (Pi.single (choiceIndex s) (1 : K) : Fin 14 → K) j) = 0 := by
    apply LagrangianGraphSpan.coefficients_eq_zero_of_graph K
    intro A
    have hr := LagrangianPrimitiveRowAction.rowFourteen_mul_symplectic
      K K (RingHom.id K) (standard K A.val) (standard_rows_isotropic K A) (swap K s)
    have hh := congrFun hr aIndex
    rw [rowFourteen_a, rowFourteen_graph, ← primitiveGL_val] at hh
    change ((standard K A.val * matrixSix K (swap K s)).submatrix id
      LagrangianMatrixChart.firstPivot).det =
      ∑ j : Fin 14, (primitiveGL K (swap K s)).val aIndex j *
        (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) j at hh
    rw [mul_swap_firstColumns, ← graph_choice_minor] at hh
    have hd : (∑ j : Fin 14, (Pi.single (choiceIndex s) (1 : K) : Fin 14 → K) j *
        (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) j) =
        (coordinateBasis14 K).equivFun (LagrangianGraphSpan.graph K A) (choiceIndex s) := by
      simp [Pi.single_apply]
    simp only [sub_mul,Finset.sum_sub_distrib]
    rw [hd,← hh,sub_self]
  funext j
  exact sub_eq_zero.mp (congrFun hz j)

/-- The actual native polynomial substitution, with no inverse or
basis conjugation, sends the original a-variable to the chosen minor. -/
theorem substitution_a_swap (s : Choice) :
    NativeProjectiveLinear.substitution K 13 (primitiveGL K (swap K s)).val (X aIndex) =
      X (choiceIndex s) := by
  rw [NativeProjectiveLinear.substitution_X,swap_a_row]
  simp [Pi.single_apply]

/-- The same literal identity after every coefficient-ring map. This
includes arbitrary nonreduced K-rings. -/
theorem substitution_a_swap_map {R : Type u} [CommRing R] (φ : K →+* R) (s : Choice) :
    NativeProjectiveLinear.substitution R 13
        ((primitiveGL K (swap K s)).val.map φ) (X aIndex) = X (choiceIndex s) := by
  have hr : ((primitiveGL K (swap K s)).val.map φ) aIndex =
      (Pi.single (choiceIndex s) (1 : R) : Fin 14 → R) := by
    funext j
    rw [Matrix.map_apply]
    rw [swap_a_row]
    simp [Pi.single_apply]
  rw [NativeProjectiveLinear.substitution_X,hr]
  simp [Pi.single_apply]

end M9Native.LagrangianAdmissibleSwapCoordinate
