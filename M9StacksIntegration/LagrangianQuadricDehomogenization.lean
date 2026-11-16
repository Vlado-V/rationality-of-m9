module

public import M9StacksIntegration.LagrangianHomogeneousQuadrics
public import M9StacksIntegration.LagrangianBlockMinorQuadrics

/-! Dehomogenizing the actual twenty-one quadrics at a=1 gives the
exact graph ideal q=adj(p), b=det(p), over every coefficient ring. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

open MvPolynomial Matrix

universe u

namespace M9Native.LagrangianQuadricDehomogenization

open LagrangianQuadricChartAlgebra

variable (R : Type u) [CommRing R]

def dehom : LagrangianHomogeneousQuadrics.Ring R →ₐ[R] LocalRing R :=
  MvPolynomial.aeval (Sum.elim (fun _ => 1)
    (Sum.elim (fun ij => X (Sum.inl (Sum.inl ij)))
      (Sum.elim (fun ij => X (Sum.inr ij))
        (fun _ => X (Sum.inl (Sum.inr ()))))))

@[simp] theorem dehom_a : dehom R (LagrangianHomogeneousQuadrics.aVariable R) = 1 := by
  simp [dehom, LagrangianHomogeneousQuadrics.aVariable]

@[simp] theorem dehom_b : dehom R (LagrangianHomogeneousQuadrics.bVariable R) = bVariable R := by
  simp [dehom, LagrangianHomogeneousQuadrics.bVariable, bVariable]

theorem dehom_pMatrix : (LagrangianHomogeneousQuadrics.pMatrix R).map (dehom R) = pMatrix R := by
  funext i j
  simp [dehom, LagrangianHomogeneousQuadrics.pMatrix, pMatrix, genericMatrix]

theorem dehom_qMatrix : (LagrangianHomogeneousQuadrics.qMatrix R).map (dehom R) = qMatrix R := by
  funext i j
  simp [dehom, LagrangianHomogeneousQuadrics.qMatrix, qMatrix]

theorem dehom_adjP (i j : Fin 3) :
    dehom R (LagrangianHomogeneousQuadrics.adjP R i j) = adjRelation R i j := by
  have h := (dehom R).map_adjugate (LagrangianHomogeneousQuadrics.pMatrix R)
  simp only [AlgHom.mapMatrix_apply] at h
  rw [dehom_pMatrix] at h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (LocalRing R) => A i j) h
  have hq := congrArg (fun A : Matrix (Fin 3) (Fin 3) (LocalRing R) => A i j) (dehom_qMatrix R)
  rw [LagrangianHomogeneousQuadrics.adjP, map_sub, map_mul, dehom_a, one_mul]
  exact congrArg₂ (· - ·) he hq

theorem dehom_adjQ (i j : Fin 3) :
    dehom R (LagrangianHomogeneousQuadrics.adjQ R i j) =
      (qMatrix R).adjugate i j - bVariable R * pMatrix R i j := by
  have h := (dehom R).map_adjugate (LagrangianHomogeneousQuadrics.qMatrix R)
  simp only [AlgHom.mapMatrix_apply] at h
  rw [dehom_qMatrix] at h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (LocalRing R) => A i j) h
  have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) (LocalRing R) => A i j) (dehom_pMatrix R)
  rw [LagrangianHomogeneousQuadrics.adjQ, map_sub, map_mul, dehom_b]
  exact congrArg₂ (· - ·) he (congrArg (bVariable R * ·) hp)

theorem dehom_product (i j : Fin 3) :
    dehom R (LagrangianHomogeneousQuadrics.product R i j) = productRelation R i j := by
  have hm : (LagrangianHomogeneousQuadrics.pMatrix R *
      LagrangianHomogeneousQuadrics.qMatrix R).map (dehom R) = pMatrix R * qMatrix R := by
    rw [Matrix.map_mul, dehom_pMatrix, dehom_qMatrix]
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (LocalRing R) => A i j) hm
  have ho : dehom R ((1 : Matrix (Fin 3) (Fin 3)
      (LagrangianHomogeneousQuadrics.Ring R)) i j) =
      (1 : Matrix (Fin 3) (Fin 3) (LocalRing R)) i j := by
    simp only [Matrix.one_apply]
    split_ifs <;> simp only [map_one, map_zero]
  rw [LagrangianHomogeneousQuadrics.product, map_sub, map_mul, map_mul,
    dehom_a, dehom_b, one_mul, ho]
  exact congrArg₂ (· - ·) he rfl

def dehomIdeal : Ideal (LocalRing R) :=
  Ideal.span (Set.range fun i : LagrangianHomogeneousQuadrics.QuadricIndex.{u} =>
    dehom R (LagrangianHomogeneousQuadrics.quadric R i))

theorem local_pMatrix_symmetric : (pMatrix R).transpose = pMatrix R := by
  rw [pMatrix, ← Matrix.transpose_map, genericMatrix_symmetric]

theorem local_qMatrix_symmetric : (qMatrix R).transpose = qMatrix R := by
  funext i j
  change (X (Sum.inl (Sum.inl (ULift.up (LagrangianMatrixChart.symmetricIndex (j,i))))) : LocalRing R) =
    X (Sum.inl (Sum.inl (ULift.up (LagrangianMatrixChart.symmetricIndex (i,j)))))
  rw [LagrangianMatrixChart.symmetricIndex_swap]

theorem adjRelation_swap (i j : Fin 3) : adjRelation R j i = adjRelation R i j := by
  have hp : (pMatrix R).adjugate.transpose = (pMatrix R).adjugate := by
    rw [Matrix.adjugate_transpose, local_pMatrix_symmetric]
  exact congrArg₂ (· - ·) (congrFun (congrFun hp i) j)
    (congrFun (congrFun (local_qMatrix_symmetric R) i) j)

theorem adjRelation_mem_dehomIdeal (i j : Fin 3) : adjRelation R i j ∈ dehomIdeal R := by
  have h : dehom R (LagrangianHomogeneousQuadrics.quadric R
      (Sum.inl (ULift.up (LagrangianMatrixChart.symmetricIndex (i,j))))) ∈ dehomIdeal R :=
    Ideal.subset_span ⟨_, rfl⟩
  change dehom R (LagrangianHomogeneousQuadrics.adjP R _ _) ∈ dehomIdeal R at h
  rw [dehom_adjP] at h
  by_cases hij : i ≤ j
  · simpa only [LagrangianMatrixChart.symmetricIndex, dite_eq_left hij] using h
  · simpa only [LagrangianMatrixChart.symmetricIndex, dite_eq_right hij, adjRelation_swap] using h

theorem quadricIdeal_le_dehomIdeal : quadricIdeal R ≤ dehomIdeal R := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl ij => exact adjRelation_mem_dehomIdeal R ij.1 ij.2
  | inr ij =>
    have h : dehom R (LagrangianHomogeneousQuadrics.quadric R
        (Sum.inr (Sum.inr ij))) ∈ dehomIdeal R := Ideal.subset_span ⟨_, rfl⟩
    change productRelation R ij.1 ij.2 ∈ dehomIdeal R
    change dehom R (LagrangianHomogeneousQuadrics.product R ij.1 ij.2) ∈ dehomIdeal R at h
    exact (dehom_product R ij.1 ij.2) ▸ h

theorem graphMap_dehom_adjQ (i j : Fin 3) :
    graphMap R (dehom R (LagrangianHomogeneousQuadrics.adjQ R i j)) = 0 := by
  have h := (graphMap R).map_adjugate (qMatrix R)
  simp only [AlgHom.mapMatrix_apply] at h
  rw [graphMap_qMatrix] at h
  have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) (AffineRing R) => A i j) h
  have hp := congrArg (fun A : Matrix (Fin 3) (Fin 3) (AffineRing R) => A i j) (graphMap_pMatrix R)
  have hadj := congrArg (fun A : Matrix (Fin 3) (Fin 3) (AffineRing R) => A i j)
    (LagrangianBlockMinorQuadrics.adjugate_adjugate_three (AffineRing R) (genericMatrix R))
  rw [dehom_adjQ, map_sub, map_mul, graphMap_bVariable]
  rw [show graphMap R ((qMatrix R).adjugate i j) = (genericMatrix R).adjugate.adjugate i j from he,
    show graphMap R (pMatrix R i j) = genericMatrix R i j from hp]
  simpa only [Matrix.smul_apply, smul_eq_mul] using sub_eq_zero.mpr hadj

theorem dehomIdeal_le_graphKernel : dehomIdeal R ≤ RingHom.ker (graphMap R).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  cases i with
  | inl ij =>
    change graphMap R (dehom R (LagrangianHomogeneousQuadrics.adjP R _ _)) = 0
    rw [dehom_adjP]
    exact graphMap_adjRelation R _ _
  | inr i =>
    cases i with
    | inl ij => exact graphMap_dehom_adjQ R _ _
    | inr ij =>
      change graphMap R (dehom R (LagrangianHomogeneousQuadrics.product R _ _)) = 0
      rw [dehom_product]
      exact graphMap_productRelation R _ _

/-- Equality of actual polynomial ideals, including all nilpotents. -/
theorem dehomIdeal_eq_graphKernel : dehomIdeal R = RingHom.ker (graphMap R).toRingHom := by
  apply le_antisymm (dehomIdeal_le_graphKernel R)
  rw [ker_graphMap_eq_quadricIdeal]
  exact quadricIdeal_le_dehomIdeal R

theorem dehomIdeal_eq_quadricIdeal : dehomIdeal R = quadricIdeal R :=
  (dehomIdeal_eq_graphKernel R).trans (ker_graphMap_eq_quadricIdeal R)

end M9Native.LagrangianQuadricDehomogenization
