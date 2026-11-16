module

public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!+# Coordinates in a pair of semilinearly exchanged vector spaces

An actual semilinear isomorphism transports a basis.  In these paired bases,
exchanging an isomorphism with its inverse conjugates its inverse matrix by the
coefficient automorphism.  This is the linear-algebra step in Section 5; the
geometric descent producing the vector spaces and exchange remains separate.
-/

@[expose] public section
noncomputable section

namespace M9.PairedSemilinearCoordinates

open Module


variable {L E F ι : Type*} [Field L] [AddCommGroup E] [Module L E]
  [AddCommGroup F] [Module L F] [Fintype ι]

/-- Scalar compatibility for an actual additive isomorphism. This is the usual
semilinearity condition, stated explicitly to retain its coefficient automorphism. -/
def IsSemilinear (σ : L ≃+* L) (u : E ≃+ F) : Prop :=
  ∀ (a : L) (e : E), u (a • e) = σ a • u e

omit [Fintype ι] in
@[simp] theorem inverse_map_smul (σ : L ≃+* L) (u : E ≃+ F)
    (hu : IsSemilinear σ u) (a : L) (f : F) :
    u.symm (a • f) = σ.symm a • u.symm f := by
  apply u.injective
  rw [u.apply_symm_apply, hu]
  simp

/-- The linear coordinate map for the images of the original basis under a
semilinear isomorphism.  The coefficient automorphism corrects semilinearity. -/
def pairedCoordinates (σ : L ≃+* L) (u : E ≃+ F) (hu : IsSemilinear σ u) (b : Basis ι L E) :
    F ≃ₗ[L] (ι → L) where
  toFun f i := σ (b.equivFun (u.symm f) i)
  invFun c := u (b.equivFun.symm (fun i => σ.symm (c i)))
  left_inv f := by simp
  right_inv c := by
    ext i
    change σ (b.equivFun (u.symm (u (b.equivFun.symm
      (fun j => σ.symm (c j))))) i) = c i
    rw [u.symm_apply_apply, b.equivFun.apply_symm_apply]
    exact σ.apply_symm_apply _
  map_add' f g := by ext i; simp
  map_smul' a f := by
    ext i
    simp [inverse_map_smul σ u hu, map_smul]

@[simp] theorem pairedCoordinates_apply (σ : L ≃+* L) (u : E ≃+ F) (hu : IsSemilinear σ u)
    (b : Basis ι L E) (f : F) (i : ι) :
    pairedCoordinates σ u hu b f i = σ (b.repr (u.symm f) i) := rfl

/-- A genuine basis of the exchanged vector space. -/
def pairedBasis (σ : L ≃+* L) (u : E ≃+ F) (hu : IsSemilinear σ u) (b : Basis ι L E) : Basis ι L F :=
  Basis.ofEquivFun (pairedCoordinates σ u hu b)

@[simp] theorem pairedBasis_repr (σ : L ≃+* L) (u : E ≃+ F) (hu : IsSemilinear σ u)
    (b : Basis ι L E) (f : F) (i : ι) :
    (pairedBasis σ u hu b).repr f i = σ (b.repr (u.symm f) i) := rfl

@[simp] theorem pairedBasis_apply (σ : L ≃+* L) (u : E ≃+ F) (hu : IsSemilinear σ u)
    (b : Basis ι L E) (i : ι) : pairedBasis σ u hu b i = u (b i) := by
  classical
  apply (pairedCoordinates σ u hu b).injective
  ext j
  change (pairedBasis σ u hu b).repr (pairedBasis σ u hu b i) j =
    σ (b.repr (u.symm (u (b i))) j)
  simp [Finsupp.single_apply]

/-- Exchange of an actual linear isomorphism, when the coefficient automorphism
is an involution. -/
def exchange (σ : L ≃+* L) (hσ : ∀ a, σ (σ a) = a)
    (u : E ≃+ F) (hu : IsSemilinear σ u) (x : E ≃ₗ[L] F) : E ≃ₗ[L] F where
  toFun e := u (x.symm (u e))
  invFun f := u.symm (x (u.symm f))
  left_inv e := by simp
  right_inv f := by simp
  map_add' e e' := by simp
  map_smul' a e := by
    rw [hu a e, x.symm.map_smul, hu (σ a) (x.symm (u e)), hσ]
    rfl

@[simp] theorem exchange_apply (σ : L ≃+* L) (hσ : ∀ a, σ (σ a) = a)
    (u : E ≃+ F) (hu : IsSemilinear σ u) (x : E ≃ₗ[L] F) (e : E) :
    exchange σ hσ u hu x e = u (x.symm (u e)) := rfl

/-- The matrix of the exchanged isomorphism is the coefficient conjugate of the
inverse map's matrix in the paired bases. -/
theorem exchange_toMatrix [DecidableEq ι] (σ : L ≃+* L) (hσ : ∀ a, σ (σ a) = a)
    (u : E ≃+ F) (hu : IsSemilinear σ u) (b : Basis ι L E) (x : E ≃ₗ[L] F) :
    LinearMap.toMatrix b (pairedBasis σ u hu b) (exchange σ hσ u hu x).toLinearMap =
      (LinearMap.toMatrix (pairedBasis σ u hu b) b x.symm.toLinearMap).map σ := by
  ext i j
  simp [LinearMap.toMatrix_apply, exchange]

omit [Fintype ι] in
@[simp] theorem exchange_exchange (σ : L ≃+* L) (hσ : ∀ a, σ (σ a) = a)
    (u : E ≃+ F) (hu : IsSemilinear σ u) (x : E ≃ₗ[L] F) :
    exchange σ hσ u hu (exchange σ hσ u hu x) = x := by
  ext e
  simp [exchange]

/-- The inverse linear isomorphism has the ordinary nonsingular inverse matrix. -/
theorem inverse_toMatrix [DecidableEq ι] (b : Basis ι L E) (c : Basis ι L F)
    (x : E ≃ₗ[L] F) :
    LinearMap.toMatrix c b x.symm.toLinearMap =
      (LinearMap.toMatrix b c x.toLinearMap)⁻¹ := by
  symm
  apply Matrix.inv_eq_left_inv
  rw [← LinearMap.toMatrix_comp b c b]
  have hc : x.symm.toLinearMap.comp x.toLinearMap = LinearMap.id := by
    ext e
    simp
  rw [hc, LinearMap.toMatrix_id]

/-- In paired bases the actual exchange is coefficient conjugation followed by
matrix inversion.  Consequently the semilinear pullback sends coordinate
functions to the entries of the inverse matrix. -/
theorem exchange_matrix_inverse [DecidableEq ι] (σ : L ≃+* L)
    (hσ : ∀ a, σ (σ a) = a) (u : E ≃+ F) (hu : IsSemilinear σ u)
    (b : Basis ι L E) (x : E ≃ₗ[L] F) :
    LinearMap.toMatrix b (pairedBasis σ u hu b) (exchange σ hσ u hu x).toLinearMap =
      ((LinearMap.toMatrix b (pairedBasis σ u hu b) x.toLinearMap)⁻¹).map σ := by
  rw [exchange_toMatrix, inverse_toMatrix]

end M9.PairedSemilinearCoordinates
