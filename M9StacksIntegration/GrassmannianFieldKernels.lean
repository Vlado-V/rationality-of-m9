module

public import M9StacksIntegration.SplitMatrixGrassmannian

/-!
# Actual field-valued Grassmannian classifiers and matrix kernels

The native quotient classifier identifies two surjective field matrices
precisely when their linear kernels agree.  The comparison is proved through
actual isomorphisms of the finite free quotient sheaves.  An arbitrary pair
of morphisms over a common base is covered when their actual quotient
classes are the given matrices.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.GrassmannianFieldKernels

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix
open SplitMatrixGrassmannian

theorem isomorphic_of_class_eq {T : Scheme.{u}} {k n : ℕ}
    {q q' : QuotientPresentation T k n}
    (h : (⟦q⟧ : Points T k n) = ⟦q'⟧) : q.Isomorphic q' := by
  have hrel := Quotient.exact h
  clear h
  induction hrel with
  | rel _ _ h => exact h
  | refl q => exact ⟨Iso.refl _, by simp⟩
  | symm q q' _ ih =>
      obtain ⟨e, he⟩ := ih
      exact ⟨e.symm, by rw [← he]; simp⟩
  | trans q q' q'' _ _ ih₁ ih₂ =>
      obtain ⟨e, he⟩ := ih₁
      obtain ⟨e', he'⟩ := ih₂
      refine ⟨e ≪≫ e', ?_⟩
      change q.map ≫ (e.hom ≫ e'.hom) = q''.map
      rw [← Category.assoc, he, he']

variable {K : Type u} [Field K] {m n : ℕ}

theorem factor_of_kernel_le (M M' : Matrix (Fin m) (Fin n) K)
    (N : Matrix (Fin n) (Fin m) K) (hMN : M * N = 1)
    (hker : LinearMap.ker M.mulVecLin ≤ LinearMap.ker M'.mulVecLin) :
    M' = (M' * N) * M := by
  have hval (x : Fin n → K) : M'.mulVec x = ((M' * N) * M).mulVec x := by
    let v := x - N.mulVec (M.mulVec x)
    have hv : M.mulVec v = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec, sub_self]
    have hv' : M'.mulVec v = 0 := hker hv
    simpa only [v, Matrix.mulVec_sub, Matrix.mulVec_mulVec, sub_eq_zero,
      Matrix.mul_assoc] using hv'
  apply Matrix.ext_of_mulVec_single
  exact fun i => hval (Pi.single i 1)

theorem exists_unit_factor_of_kernel_eq (M M' : Matrix (Fin m) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec)
    (hker : LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin) :
    ∃ A : Matrix (Fin m) (Fin m) K, IsUnit A.det ∧ M' = A * M := by
  obtain ⟨N, hN⟩ := Matrix.mulVec_surjective_iff_exists_right_inverse.mp hM
  let A := M' * N
  have heq : M' = A * M := factor_of_kernel_le M M' N hN hker.le
  have hA : Function.Surjective A.mulVec := by
    intro y
    obtain ⟨x, hx⟩ := hM' y
    refine ⟨M.mulVec x, ?_⟩
    rw [Matrix.mulVec_mulVec, ← heq, hx]
  exact ⟨A, (Matrix.isUnit_iff_isUnit_det _).mp
    (Matrix.mulVec_surjective_iff_isUnit.mp hA), heq⟩

theorem kernel_eq_of_mutual_factors (M M' : Matrix (Fin m) (Fin n) K)
    (A B : Matrix (Fin m) (Fin m) K) (hA : M' = A * M) (hB : M = B * M') :
    LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin := by
  apply le_antisymm
  · intro x hx
    change M.mulVec x = 0 at hx
    change M'.mulVec x = 0
    rw [hA, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  · intro x hx
    change M'.mulVec x = 0 at hx
    change M.mulVec x = 0
    rw [hB, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

variable (k n : ℕ) (K)

theorem fieldPresentation_isomorphic_of_kernel_eq
    (M M' : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec)
    (hker : LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin) :
    (fieldPresentation k n K M hM).Isomorphic (fieldPresentation k n K M' hM') := by
  obtain ⟨A, hA, heq⟩ := exists_unit_factor_of_kernel_eq M M' hM hM' hker
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  let a : F (Spec (.of K)) (n-k) ⟶ F (Spec (.of K)) (n-k) := ofMatrix (A.map κ)
  have ha : IsIso a := by
    apply (isIso_iff_isUnit_det a).mpr
    rw [show toMatrix a = A.map κ from toMatrix_ofMatrix _]
    change IsUnit (κ.mapMatrix A).det
    rw [← RingHom.map_det]
    exact hA.map κ
  let := ha
  refine ⟨asIso a, ?_⟩
  apply toMatrix_injective
  rw [toMatrix_comp, fieldPresentation_matrix, fieldPresentation_matrix]
  change toMatrix a * M.map κ = M'.map κ
  rw [show toMatrix a = A.map κ from toMatrix_ofMatrix _]
  rw [← Matrix.map_mul, ← heq]

theorem kernel_eq_of_fieldPresentation_isomorphic
    (M M' : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec)
    (h : (fieldPresentation k n K M hM).Isomorphic
      (fieldPresentation k n K M' hM')) :
    LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin := by
  obtain ⟨e, he⟩ := h
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  let ι := (Scheme.ΓSpecIso (.of K)).hom.hom
  let a : F (Spec (.of K)) (n-k) ⟶ F (Spec (.of K)) (n-k) := e.hom
  let b : F (Spec (.of K)) (n-k) ⟶ F (Spec (.of K)) (n-k) := e.inv
  have he' : (fieldPresentation k n K M' hM').map ≫ b =
      (fieldPresentation k n K M hM).map := by
    rw [← he]
    simp [b]
  have hA : toMatrix a * M.map κ = M'.map κ := by
    simpa only [toMatrix_comp, fieldPresentation_matrix] using congrArg toMatrix he
  have hB : toMatrix b * M'.map κ = M.map κ := by
    simpa only [toMatrix_comp, fieldPresentation_matrix] using congrArg toMatrix he'
  have hικ (x : K) : ι (κ x) = x := by
    exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f.hom x)
      (Scheme.ΓSpecIso (.of K)).inv_hom_id
  have hmap (P : Matrix (Fin (n-k)) (Fin n) K) : (P.map κ).map ι = P := by
    ext i j
    exact hικ _
  have hA' : M' = (toMatrix a).map ι * M := by
    have h := congrArg (fun P => P.map ι) hA
    rw [Matrix.map_mul, hmap M, hmap M'] at h
    exact h.symm
  have hB' : M = (toMatrix b).map ι * M' := by
    have h := congrArg (fun P => P.map ι) hB
    rw [Matrix.map_mul, hmap M', hmap M] at h
    exact h.symm
  exact kernel_eq_of_mutual_factors M M' _ _ hA' hB'

theorem fieldPresentation_class_eq_iff_kernel_eq
    (M M' : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec) :
    (⟦fieldPresentation k n K M hM⟧ : Points (Spec (.of K)) k n) =
      ⟦fieldPresentation k n K M' hM'⟧ ↔
        LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin := by
  constructor
  · intro h
    exact kernel_eq_of_fieldPresentation_isomorphic (k:=k) (n:=n) (K:=K) M M' hM hM'
      (isomorphic_of_class_eq h)
  · intro h
    exact Quotient.sound (.rel _ _
      (fieldPresentation_isomorphic_of_kernel_eq (k:=k) (n:=n) (K:=K) M M' hM hM' h))

variable {B : Type u} [Field B]

/-- Equality of actual morphisms over a common base is detected by the kernels
of their original, represented field-matrix quotient classes. -/
theorem points_eq_iff_kernel_eq
    (q q' : Spec (.of K) ⟶ GrassmannianCharts.space B k n)
    (M M' : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec)
    (hq : (functorData k n).objEquiv (Spec (.of K))
      ((schemeRepresentableBy k n).homEquiv (q ≫ GrassmannianCharts.toIntegral B k n)) =
        ⟦fieldPresentation k n K M hM⟧)
    (hq' : (functorData k n).objEquiv (Spec (.of K))
      ((schemeRepresentableBy k n).homEquiv (q' ≫ GrassmannianCharts.toIntegral B k n)) =
        ⟦fieldPresentation k n K M' hM'⟧)
    (hbase : q ≫ GrassmannianCharts.projection B k n =
      q' ≫ GrassmannianCharts.projection B k n) :
    q = q' ↔ LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin := by
  rw [← fieldPresentation_class_eq_iff_kernel_eq (k:=k) (n:=n) (K:=K) M M' hM hM', ← hq, ← hq']
  constructor
  · rintro rfl
    rfl
  · intro h
    apply pullback.hom_ext hbase
    exact (schemeRepresentableBy k n).homEquiv.injective
      (((functorData k n).objEquiv (Spec (.of K))).injective h)

theorem fieldPoint_eq_iff_kernel_eq
    (M M' : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective M.mulVec) (hM' : Function.Surjective M'.mulVec) :
    fieldPoint k n K M hM = fieldPoint k n K M' hM' ↔
      LinearMap.ker M.mulVecLin = LinearMap.ker M'.mulVecLin :=
  points_eq_iff_kernel_eq (k:=k) (n:=n) (K:=K) _ _ M M' hM hM'
    (fieldPoint_class k n K M hM) (fieldPoint_class k n K M' hM') (by simp)

end M9Native.GrassmannianFieldKernels
