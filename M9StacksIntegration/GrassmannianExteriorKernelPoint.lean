module

public import M9StacksIntegration.GrassmannianExteriorFieldCoordinates
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# An actual independent triple in the kernel of exterior evaluation

The genuine native Grassmannian intersection supplies a closed point. Over
the original algebraically closed field this gives an actual field point,
which lies on a genuine quotient chart. Its normalized chart matrix has
identity pivot columns, so its three original rows are independent. The
checked native coordinate transport turns the projective equations into
vanishing of their actual exterior product under the given linear map.
Neither a decomposable kernel vector nor an independent triple is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module

namespace M9Native.GrassmannianExteriorKernelPoint
open GrassmannianExteriorIntersection GrassmannianExteriorFieldCoordinates
open LagrangianPluckerClosed
universe u
variable (K : Type u) [Field K]
variable {H : Type u} [AddCommGroup H] [Module K H]

/-- The field row trivector is the literal alternating product of the
three actual matrix rows. -/
theorem rowPlucker_eq_ιMulti (A : Matrix (Fin 3) (Fin 6) K) :
    LagrangianField.rowPlucker K A = exteriorPower.ιMulti K 3 (fun i => A i) := by
  unfold LagrangianField.rowPlucker LagrangianField.wedge3
  congr 1
  funext i
  fin_cases i <;> rfl

variable [IsAlgClosed K]

/-- A rank-nine actual exterior evaluation has an actual independent
original triple with nonzero exterior product in its kernel. -/
theorem exists_independent_triple (D : Exterior K →ₗ[K] H)
    (hD : finrank K (LinearMap.range D) = 9) :
    ∃ s : Fin 3 → (Fin 6 → K), LinearIndependent K s ∧
      exteriorPower.ιMulti K 3 s ≠ 0 ∧ D (exteriorPower.ιMulti K 3 s) = 0 := by
  obtain ⟨x, hxc, hx⟩ := exists_closed_point K D hD
  let q := LagrangianGrassmannian.grassmannianProjection K
  letI : Smooth q := Grassmannian.smooth_schemeOver 3 6 (Spec (.of K))
  let p : Spec (.of K) ⟶ grass K := pointOfClosedPoint q x hxc
  have hp : p ≫ q = 𝟙 _ := pointOfClosedPoint_comp q x hxc
  have hp_apply (a : Spec (.of K)) : p a = x := pointOfClosedPoint_apply q x hxc a
  let t : grass K ⟶ Grassmannian.scheme 3 6 := pullback.snd _ _
  obtain ⟨ι, z, hz⟩ := Grassmannian.exists_mem_range_chart 3 6 (t x)
  have hrange : Set.range (p ≫ t) ⊆ Set.range (Grassmannian.chart 3 6 ι) := by
    rintro _ ⟨a, rfl⟩
    change t (p a) ∈ Set.range (Grassmannian.chart 3 6 ι)
    rw [hp_apply]
    exact ⟨z, hz⟩
  let g := IsOpenImmersion.lift (Grassmannian.chart 3 6 ι) (p ≫ t) hrange
  have hpg : p ≫ pullback.snd _ _ = g ≫ Grassmannian.chart 3 6 ι :=
    (IsOpenImmersion.lift_fac (Grassmannian.chart 3 6 ι) (p ≫ t) hrange).symm
  let A := matrixOnField K ι g
  have hzero : D (LagrangianField.rowPlucker K A) = 0 := by
    apply (nativePoint_mem_iff K D p hp ι g hpg (IsLocalRing.closedPoint K)).mp
    rw [hp_apply]
    exact hx
  have hminor : (A.submatrix id ι).det ≠ 0 := by
    rw [matrixOnField_pivots, Matrix.det_one]
    exact one_ne_zero
  refine ⟨(fun i => A i), matrixOnField_rows_independent K ι g, ?_, ?_⟩
  · rw [← rowPlucker_eq_ιMulti K A]
    exact LagrangianField.rowPlucker_ne_zero_of_minor K A ι hminor
  · rwa [← rowPlucker_eq_ιMulti K A]

end M9Native.GrassmannianExteriorKernelPoint
