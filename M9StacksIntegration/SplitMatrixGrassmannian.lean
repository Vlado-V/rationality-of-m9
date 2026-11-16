module

public import M9StacksIntegration.GrassmannianCharts
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Actual native Grassmannian points from split quotient matrices

A proved rectangular matrix right inverse supplies an actual split map of
finite free sheaves.  The original native representing equivalence then
constructs the Grassmannian morphism and retains its exact quotient class.
Over a field, surjectivity supplies the right inverse by a proved matrix
theorem.  No Grassmannian point or quotient-class assertion is assumed.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.SplitMatrixGrassmannian

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix

variable (T : Scheme.{u}) (k n : ℕ)

/-- The literal quotient map of the actual finite free sheaves. -/
def quotientMap (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤)) :
    F T n ⟶ F T (n-k) := ofMatrix M

/-- The literal splitting map of the actual finite free sheaves. -/
def splittingMap (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) :
    F T (n-k) ⟶ F T n := ofMatrix N

theorem splittingMap_quotientMap
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    splittingMap T k n N ≫ quotientMap T k n M = 𝟙 _ := by
  apply toMatrix_injective
  simp only [splittingMap, quotientMap, toMatrix_comp, toMatrix_ofMatrix, toMatrix_id, hMN]

theorem quotientMap_epi
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    Epi (quotientMap T k n M) := by
  have : Epi (splittingMap T k n N ≫ quotientMap T k n M) := by
    rw [splittingMap_quotientMap T k n M N hMN]
    infer_instance
  exact epi_of_epi (splittingMap T k n N) (quotientMap T k n M)

/-- The actual native quotient presentation with its actual splitting proof. -/
def presentation (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    QuotientPresentation T k n where
  target := F T (n-k)
  map := quotientMap T k n M
  map_epi := quotientMap_epi T k n M N hMN
  finiteLocallyFree := free_isFiniteLocallyFreeOfRank T (n-k)

/-- The actual representing morphism to the native integral Grassmannian. -/
def integralMap (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) : T ⟶ scheme.{u} k n :=
  (schemeRepresentableBy k n).homEquiv.symm
    (((functorData k n).objEquiv T).symm ⟦presentation T k n M N hMN⟧)

/-- The exact quotient class of the actual representing morphism. -/
theorem integralMap_class (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    (functorData k n).objEquiv T
      ((schemeRepresentableBy k n).homEquiv (integralMap T k n M N hMN)) =
        ⟦presentation T k n M N hMN⟧ := by
  simp only [integralMap, Equiv.apply_symm_apply]

variable (K : Type u) [Field K]

/-- The actual Grassmannian morphism over the specified base field. -/
def map (p : T ⟶ Spec (.of K))
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    T ⟶ GrassmannianCharts.space K k n :=
  pullback.lift p (integralMap T k n M N hMN) (terminal.hom_ext _ _)

@[reassoc (attr := simp)] theorem map_projection (p : T ⟶ Spec (.of K))
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    map T k n K p M N hMN ≫ GrassmannianCharts.projection K k n = p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem map_toIntegral (p : T ⟶ Spec (.of K))
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    map T k n K p M N hMN ≫ GrassmannianCharts.toIntegral K k n = integralMap T k n M N hMN :=
  pullback.lift_snd _ _ _

theorem map_class (p : T ⟶ Spec (.of K))
    (M : Matrix (Fin (n-k)) (Fin n) Γ(T, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(T, ⊤)) (hMN : M * N = 1) :
    (functorData k n).objEquiv T ((schemeRepresentableBy k n).homEquiv
      (map T k n K p M N hMN ≫ GrassmannianCharts.toIntegral K k n)) =
        ⟦presentation T k n M N hMN⟧ := by
  rw [map_toIntegral]
  exact integralMap_class T k n M N hMN

/-- A surjective field matrix has an actual rectangular right inverse. -/
def fieldRightInverse (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) : Matrix (Fin n) (Fin (n-k)) K :=
  Classical.choose (Matrix.mulVec_surjective_iff_exists_right_inverse.mp hM)

theorem fieldRightInverse_spec (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) : M * fieldRightInverse k n K M hM = 1 :=
  Classical.choose_spec (Matrix.mulVec_surjective_iff_exists_right_inverse.mp hM)

/-- The proved splitting retains its literal matrix under every actual
coefficient ring homomorphism. -/
theorem fieldRightInverse_map_spec {R : Type*} [CommRing R] (κ : K →+* R)
    (M : Matrix (Fin (n-k)) (Fin n) K) (hM : Function.Surjective (Matrix.mulVec M)) :
    M.map κ * (fieldRightInverse k n K M hM).map κ = 1 := by
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero κ) (map_one κ)] using
    congrArg (fun A => A.map κ) (fieldRightInverse_spec k n K M hM)

/-- The actual quotient presentation of the original surjective field
matrix, with its literal global-section coefficient map. -/
def fieldPresentation (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) : QuotientPresentation (Spec (.of K)) k n :=
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  presentation (Spec (.of K)) k n (M.map κ) ((fieldRightInverse k n K M hM).map κ)
    (fieldRightInverse_map_spec k n K κ M hM)

theorem fieldPresentation_matrix (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) :
    toMatrix (fieldPresentation k n K M hM).map = M.map (Scheme.ΓSpecIso (.of K)).inv.hom :=
  toMatrix_ofMatrix _

/-- The original surjective field matrix gives an actual field-valued
point of the native Grassmannian, using the actual global-section map. -/
def fieldPoint (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) :
    Spec (.of K) ⟶ GrassmannianCharts.space K k n :=
  let κ := (Scheme.ΓSpecIso (.of K)).inv.hom
  map (Spec (.of K)) k n K (𝟙 _) (M.map κ) ((fieldRightInverse k n K M hM).map κ)
    (fieldRightInverse_map_spec k n K κ M hM)

/-- The actual native quotient class of this actual field point is the
original field-matrix quotient, with no assumed classifying identity. -/
theorem fieldPoint_class (M : Matrix (Fin (n-k)) (Fin n) K)
    (hM : Function.Surjective (Matrix.mulVec M)) :
    (functorData k n).objEquiv (Spec (.of K)) ((schemeRepresentableBy k n).homEquiv
      (fieldPoint k n K M hM ≫ GrassmannianCharts.toIntegral K k n)) =
        ⟦fieldPresentation k n K M hM⟧ :=
  map_class (Spec (.of K)) k n K (𝟙 _) _ _ _

@[reassoc (attr := simp)] theorem fieldPoint_projection
    (M : Matrix (Fin (n-k)) (Fin n) K) (hM : Function.Surjective (Matrix.mulVec M)) :
    fieldPoint k n K M hM ≫ GrassmannianCharts.projection K k n = 𝟙 _ :=
  map_projection (Spec (.of K)) k n K (𝟙 _) _ _ _

end M9Native.SplitMatrixGrassmannian
