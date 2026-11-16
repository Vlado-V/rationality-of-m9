module

public import M9StacksIntegration.LinearIncidenceTensorCoordinates
public import Mathlib.LinearAlgebra.BilinearMap

/-! Finite matrix contraction for the actual sheaf tensor of sections. The
coefficient matrices are inverse on the retained original free module. This
helper keeps the actual bundle isomorphisms and tensor sections, and does not
supply a geometric section-covariance law. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Matrix
open scoped BigOperators TensorProduct
universe u v

namespace M9Native.LinearIncidenceTensorCovariance

open LinearIncidenceTensorCoordinates

/-- The contraction of a bilinear pairing is unchanged by inverse coefficient
matrices, with the quotient coefficients indexed by columns. -/
theorem bilinear_contraction {R : Type u} [CommRing R]
    {P Q W : Type v} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] [AddCommGroup W] [Module R W]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : P →ₗ[R] Q →ₗ[R] W) (M N : Matrix ι ι R) (hNM : N * M = 1)
    (s : ι → P) (t : ι → Q) :
    (∑ i, B (∑ j, M i j • s j) (∑ k, N k i • t k)) = ∑ i, B (s i) (t i) := by
  calc
    _ = ∑ i, ∑ k, ∑ j, (N k i * M i j) • B (s j) (t k) := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.smul_sum, smul_smul]
    _ = ∑ k, ∑ j, ∑ i, (N k i * M i j) • B (s j) (t k) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ j, (N * M) k j • B (s j) (t k) := by
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_smul]
      rfl
    _ = _ := by simp [hNM, Matrix.one_apply]

/-- The original tensor-section construction is genuinely bilinear over the
original ring of global functions. -/
def tensorPairing (X : Scheme.{u}) (A B : X.Modules) :
    Γ(A, ⊤) →ₗ[Γ(X, ⊤)] Γ(B, ⊤) →ₗ[Γ(X, ⊤)] Γ(tensorObj X A B, ⊤) :=
  (TensorProduct.mk Γ(X, ⊤) Γ(A, ⊤) Γ(B, ⊤)).compr₂
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify X.sheaf.obj
      X.ringCatSheaf.property (PresheafOfModules.tensorObj A.val B.val)).app (op ⊤)).hom

@[simp] theorem tensorPairing_apply (X : Scheme.{u}) (A B : X.Modules)
    (s : Γ(A, ⊤)) (t : Γ(B, ⊤)) :
    tensorPairing X A B s t = tensorTop X A B s t := rfl

/-- Actual isomorphisms in both factors induce the actual tensor isomorphism. -/
def tensorTransport {X : Scheme.{u}} {A' A B' B : X.Modules}
    (e : A' ≅ A) (d : B' ≅ B) : tensorObj X A' B' ≅ tensorObj X A B :=
  Stacks.SheafOfModules.Invertible.tensorProductIso X.sheaf.obj X.ringCatSheaf.property e d

theorem tensorTransport_apply {X : Scheme.{u}} {A' A B' B : X.Modules}
    (e : A' ≅ A) (d : B' ≅ B) (s : Γ(A', ⊤)) (t : Γ(B', ⊤)) :
    (tensorTransport e d).hom.app ⊤ (tensorTop X A' B' s t) =
      tensorTop X A B (e.hom.app ⊤ s) (d.hom.app ⊤ t) :=
  Stacks.SheafOfModules.tensorSections_tensorProductIsoAt X.sheaf.obj X.ringCatSheaf.property
    (op ⊤) _ _ _ _ e d s t

/-- The native standard basis has the literal identity matrix of coordinates. -/
theorem freeBasis_coordinates (X : Scheme.{u}) (n : ℕ) (i j : Fin n) :
    LagrangianMatrixChart.freeSectionCoordinates X n
      (LagrangianMatrixChart.freeBasisSection X n i) j = (1 : Matrix (Fin n) (Fin n) Γ(X, ⊤)) j i := by
  have h := LagrangianMatrixChart.freeCoordinates_map_basis
    (𝟙 (LagrangianMatrixChart.freeOn X n)) j i
  change LagrangianMatrixChart.freeSectionCoordinates X n
    (LagrangianMatrixChart.freeBasisSection X n i) j = _ at h
  exact h.trans (congrArg (fun M : Matrix (Fin n) (Fin n) Γ(X, ⊤) => M j i)
    (Stacks.FreeSheafMatrix.toMatrix_id (X := X) n))

/-- Every global section of the actual finite free sheaf is the sum of its
literal native basis sections with its actual coordinate coefficients. -/
theorem freeSection_decomposition (X : Scheme.{u}) (n : ℕ)
    (s : Γ(LagrangianMatrixChart.freeOn X n, ⊤)) :
    s = ∑ i : Fin n, LagrangianMatrixChart.freeSectionCoordinates X n s i •
      LagrangianMatrixChart.freeBasisSection X n i := by
  classical
  apply (LagrangianMatrixChart.freeSectionCoordinates X n).injective
  funext j
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    freeBasis_coordinates, Matrix.one_apply]
  simp

/-- An actual free-sheaf endomorphism followed by an actual quotient has
exactly the column expansion of the original matrix, without choosing a frame
of the quotient. -/
theorem freeMap_basis_expansion {X : Scheme.{u}} {Q : X.Modules} (n : ℕ)
    (A : LagrangianMatrixChart.freeOn X n ⟶ LagrangianMatrixChart.freeOn X n)
    (q : LagrangianMatrixChart.freeOn X n ⟶ Q) (i : Fin n) :
    (A ≫ q).app ⊤ (LagrangianMatrixChart.freeBasisSection X n i) =
      ∑ k : Fin n, Stacks.FreeSheafMatrix.toMatrix A k i •
        q.app ⊤ (LagrangianMatrixChart.freeBasisSection X n k) := by
  change q.app ⊤ (A.app ⊤ (LagrangianMatrixChart.freeBasisSection X n i)) = _
  conv_lhs => rw [freeSection_decomposition X n
    (A.app ⊤ (LagrangianMatrixChart.freeBasisSection X n i))]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Scheme.Modules.Hom.app_smul]
  exact congrArg (fun c => c • q.app ⊤ (LagrangianMatrixChart.freeBasisSection X n k))
    (LagrangianMatrixChart.freeCoordinates_map_basis A k i)

/-- The canonical actual pullback/tensor comparison retains the original
finite sum and each of its literal pure tensor sections. -/
theorem pullbackTensor_sum {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules)
    {ι : Type*} [Fintype ι] (s : ι → Γ(A, ⊤)) (t : ι → Γ(B, ⊤)) :
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso f A B).hom.app ⊤
      (pullbackGlobalSections f (tensorObj Y A B) (∑ i, tensorTop Y A B (s i) (t i))) =
    ∑ i, tensorTop X ((Scheme.Modules.pullback f).obj A)
      ((Scheme.Modules.pullback f).obj B)
      (pullbackGlobalSections f A (s i)) (pullbackGlobalSections f B (t i)) := by
  rw [map_sum, map_sum]
  exact Finset.sum_congr rfl fun i _ =>
    Stacks.PullbackTensorIso.pullbackGlobalSections_tensorSectionsAt f A B (s i) (t i)

/-- The actual finite incidence tensor sum is preserved after transporting
both bundles and cancelling the actual inverse matrices. -/
theorem tensorTransport_sum {X : Scheme.{u}} {A' A B' B : X.Modules}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : A' ≅ A) (d : B' ≅ B) (M N : Matrix ι ι Γ(X, ⊤)) (hNM : N * M = 1)
    (s' : ι → Γ(A', ⊤)) (t' : ι → Γ(B', ⊤))
    (s : ι → Γ(A, ⊤)) (t : ι → Γ(B, ⊤))
    (hs : ∀ i, e.hom.app ⊤ (s' i) = ∑ j, M i j • s j)
    (ht : ∀ i, d.hom.app ⊤ (t' i) = ∑ k, N k i • t k) :
    (tensorTransport e d).hom.app ⊤ (∑ i, tensorTop X A' B' (s' i) (t' i)) =
      ∑ i, tensorTop X A B (s i) (t i) := by
  rw [map_sum]
  simp only [tensorTransport_apply, hs, ht]
  exact bilinear_contraction (tensorPairing X A B) M N hNM s t

end M9Native.LinearIncidenceTensorCovariance
