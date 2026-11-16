module

public import M9StacksIntegration.MukaiConormalClosedPoint
public import M9StacksIntegration.LagrangianSigmaInvariance

/-!
# Genuine closed-point normalization of the complete evaluation

Global generation and the actual exterior-square relation make the
original closed-point evaluation a surjective isotropic quotient. Native
symplectic transitivity then constructs a complete H0 basis in which it
is literally the standard quotient. The exterior-square relation is
preserved by the actual symplectic bivector-invariance theorem.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Module Matrix

universe u

namespace M9Native.MukaiConormalNormalization

open LagrangianField LagrangianTransitivity MukaiLagrangianMap

variable (k : Type u) [Field k]

theorem standardProjection_eq :
    (standardQuotient k).mulVecLin = MukaiSchubertCone.firstProjection k := by
  apply (Pi.basisFun k (Fin 6)).ext
  intro j
  ext i
  refine Fin.addCases (m := 3) (n := 3) (fun j => ?_) (fun j => ?_) j
  · simp [MukaiSchubertCone.firstProjection, eIndex, Pi.single_apply, Fin.ext_iff]
  · have hne : eIndex i ≠ j.addNat 3 := by
      intro he
      have hv := congrArg Fin.val he
      simp only [eIndex, Fin.val_castAdd, Fin.val_addNat] at hv
      have hi := i.isLt
      omega
    simpa [MukaiSchubertCone.firstProjection, Pi.single_apply, hne] using
      standardQuotient_last k i j

variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (E : X.Modules)
    (b : Basis (Fin 6) k (cohomologyOverField k f E 0))

theorem basisSigma_eq_map :
    basisSigma k f E b = exteriorPower.map 2 b.equivFun.symm.toLinearMap (sigma k) := by
  simp only [basisSigma, sigma, map_sum, exteriorPower.map_apply_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext j
  fin_cases j <;> simp [LagrangianField.e, LagrangianField.f, basisVector, eIndex, fIndex]

theorem kernelMatrix_basisSigma :
    MukaiWedgeKernel.kernelMatrix k f E b (basisSigma k f E b) = standardMatrix k := by
  have h : MukaiWedgeKernel.coordinateBivector k f E b (basisSigma k f E b) =
      standardSigma k := by
    simp only [MukaiWedgeKernel.coordinateBivector, basisSigma, standardSigma, map_sum,
      exteriorPower.map_apply_ιMulti]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    ext j
    fin_cases j <;> simp [Pi.single_apply, eq_comm]
  change MukaiWedgeKernel.bivectorMatrix k 6
    (MukaiWedgeKernel.coordinateBivector k f E b (basisSigma k f E b)) = _
  rw [h, standardSigma_matrix]

variable [IsAlgClosed k] [LocallyOfFiniteType f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

theorem closedMatrix_eq_evaluation (x : X) (hx : IsClosed ({x} : Set X)) :
    (closedMatrix k f E b x hx).mulVecLin =
      (MukaiSemiExclusions.closedEvaluation k f E x hx).comp b.equivFun.symm.toLinearMap := by
  apply (Pi.basisFun k (Fin 6)).ext
  intro j
  ext i
  simp [closedMatrix, Pi.basisFun_apply]

theorem closedMatrix_rows_isotropic
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∀ i j, LagrangianRing.omega k (closedMatrix k f E b x hx i)
      (closedMatrix k f E b x hx j) = 0 := by
  let M := closedMatrix k f E b x hx
  have hm := closedMatrix_isotropic k f E b x hx (basisSigma k f E b) hσ
  rw [kernelMatrix_basisSigma] at hm
  intro i j
  have hb : (standardMatrix k).toBilin' (M i) (M j) = 0 := by
    have h := congrFun (congrFun hm i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Finset.sum_mul] at h
    rw [Finset.sum_comm] at h
    simpa only [Matrix.toBilin'_apply, M] using h
  rw [show standardMatrix k = -standardForm k from rfl, map_neg] at hb
  change -(standardForm k).toBilin' (M i) (M j) = 0 at hb
  rw [standardForm_bilin, neg_neg] at hb
  exact hb

theorem exists_normalized_basis
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ a : Basis (Fin 6) k (cohomologyOverField k f E 0),
      ExteriorEvaluation.lambda k f E 2 (basisSigma k f E a) = 0 ∧
      ∀ v : V k, MukaiSemiExclusions.closedEvaluation k f E x hx (a.equivFun.symm v) =
        MukaiSchubertCone.firstProjection k v := by
  let M := closedMatrix k f E b x hx
  obtain ⟨g,hg⟩ := exists_matrix_normalForm k M
    (closedMatrix_surjective k f E b hgen x hx)
    (closedMatrix_rows_isotropic k f E b hσ x hx)
  let a : Basis (Fin 6) k (cohomologyOverField k f E 0) :=
    Basis.ofEquivFun (b.equivFun.trans (symplecticEquiv k g).symm)
  have ha : a.equivFun.symm = (symplecticEquiv k g).trans b.equivFun.symm := by
    dsimp only [a]
    rw [Basis.equivFun_ofEquivFun]
    rfl
  refine ⟨a,?_,?_⟩
  · have hs : basisSigma k f E a = basisSigma k f E b := by
      rw [basisSigma_eq_map, basisSigma_eq_map, ha]
      change exteriorPower.map 2 (b.equivFun.symm.toLinearMap.comp
        (symplecticEquiv k g).toLinearMap) (sigma k) = _
      rw [exteriorPower.map_comp, LinearMap.comp_apply,
        LagrangianSigmaInvariance.symplecticEquiv_preserves_sigma]
    rw [hs]
    exact hσ
  · intro v
    rw [ha]
    change MukaiSemiExclusions.closedEvaluation k f E x hx
      (b.equivFun.symm (symplecticEquiv k g v)) = _
    calc
      _ = M *ᵥ (symplecticEquiv k g v) :=
        (LinearMap.congr_fun (closedMatrix_eq_evaluation k f E b x hx)
          (symplecticEquiv k g v)).symm
      _ = (M * matrixSix k g) *ᵥ v := Matrix.mulVec_mulVec v M (matrixSix k g)
      _ = (standardQuotient k) *ᵥ v := by rw [hg]
      _ = MukaiSchubertCone.firstProjection k v :=
        LinearMap.congr_fun (standardProjection_eq k) v

section

variable [CharZero k] [IsIntegral X]

/-- At EVERY actual closed point, a genuine complete-section basis is
constructed whose actual primitive-evaluation/conormal intersection
avoids the cubic discriminant and has dimension at most one. Neither
the normalized basis nor discriminant avoidance is an input. -/
theorem exists_basis_avoiding_discriminant
    (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (hσ : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ a : Basis (Fin 6) k (cohomologyOverField k f E 0),
      ExteriorEvaluation.lambda k f E 2 (basisSigma k f E a) = 0 ∧
      Module.finrank k (MukaiConormalClosedPoint.originIntersection k f E a) ≤ 1 ∧
      ∀ v ∈ MukaiConormalClosedPoint.originIntersection k f E a,
        v ≠ 0 → MukaiConormalPencil.discriminant v ≠ 0 := by
  obtain ⟨a,ha,hnorm⟩ := exists_normalized_basis k f E b hgen hσ x hx
  refine ⟨a,ha,MukaiConormalClosedPoint.finrank_originIntersection_le_one
    k f E a ha hsemi x hx hnorm,?_⟩
  intro v hv hn
  exact MukaiConormalClosedPoint.discriminant_ne_zero_of_kernel
    k f E a ha hsemi x hx hnorm v hn hv

end

end M9Native.MukaiConormalNormalization
