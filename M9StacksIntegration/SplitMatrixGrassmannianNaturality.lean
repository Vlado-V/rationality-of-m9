module

public import M9StacksIntegration.SplitMatrixGrassmannian
public import M9StacksIntegration.PrimitiveFreeMatrixPullback

/-!
# Pullback naturality of the actual split-matrix Grassmannian classifier

Canonical pullback of the source and target free sheaves carries a rectangular
matrix entrywise through the actual map on global functions.  This gives an
isomorphism of the original quotient presentations and, by the native
representing equivalence, equality of the actual classifying morphisms.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

universe u

namespace M9Native.SplitMatrixGrassmannianNaturality

open AlgebraicGeometry.Grassmannian Stacks.FreeSheafMatrix
open LagrangianMatrixChart LagrangianGrassmannian LagrangianFreeMatrixPullback
open PrimitiveFreeMatrixPullback SectionZeroIdealFactorization SplitMatrixGrassmannian

theorem freeMap_column_eq_sum (X : Scheme.{u}) {a b : ℕ}
    (q : freeOn X a ⟶ freeOn X b) (j : Fin a) :
    q.app ⊤ (freeBasisSection X a j) =
      ∑ i : Fin b, toMatrix q i j • freeBasisSection X b i := by
  have hc (i : Fin b) : freeSectionCoordinates X b (q.app ⊤ (freeBasisSection X a j)) i =
      toMatrix q i j := freeCoordinates_map_basis q i j
  simpa only [hc] using eq_sum_coordinates_basis X b (q.app ⊤ (freeBasisSection X a j))

/-- Actual pullback of a rectangular free-sheaf map, in the canonical free trivializations. -/
def pulledFreeMap {X Y : Scheme.{u}} (f : Y ⟶ X) {a b : ℕ}
    (q : freeOn X a ⟶ freeOn X b) : freeOn Y a ⟶ freeOn Y b :=
  (pullbackFreeIso f a).inv ≫ (Scheme.Modules.pullback f).map q ≫ (pullbackFreeIso f b).hom

theorem pulledFreeMap_column {X Y : Scheme.{u}} (f : Y ⟶ X) {a b : ℕ}
    (q : freeOn X a ⟶ freeOn X b) (j : Fin a) :
    (pulledFreeMap f q).app ⊤ (freeBasisSection Y a j) =
      ∑ i : Fin b, f.appTop (toMatrix q i j) • freeBasisSection Y b i := by
  change (pullbackFreeIso f b).hom.app ⊤
    (((Scheme.Modules.pullback f).map q).app ⊤
      ((pullbackFreeIso f a).inv.app ⊤ (freeBasisSection Y a j))) = _
  rw [inverse_freeBasisSection_pullback, pullback_map_app_pullbackGlobalSections, freeMap_column_eq_sum]
  simp only [map_sum, AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul,
    Scheme.Modules.Hom.app_smul, freeBasisSection_pullback]

/-- The actual canonical free pullback sends every rectangular matrix entrywise. -/
theorem pulledFreeMap_matrix {X Y : Scheme.{u}} (f : Y ⟶ X) {a b : ℕ}
    (q : freeOn X a ⟶ freeOn X b) :
    toMatrix (pulledFreeMap f q) = (toMatrix q).map f.appTop.hom := by
  ext i j
  rw [← freeCoordinates_map_basis (pulledFreeMap f q) i j]
  change freeSectionCoordinates Y b ((pulledFreeMap f q).app ⊤ (freeBasisSection Y a j)) i = _
  rw [pulledFreeMap_column]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, freeCoordinates_basis]
  simp

theorem pulledFreeMap_ofMatrix {X Y : Scheme.{u}} (f : Y ⟶ X) {a b : ℕ}
    (M : Matrix (Fin b) (Fin a) Γ(X, ⊤)) :
    pulledFreeMap f (ofMatrix M) = ofMatrix (M.map f.appTop.hom) := by
  apply toMatrix_injective
  rw [pulledFreeMap_matrix, toMatrix_ofMatrix, toMatrix_ofMatrix]

theorem rightInverse_map {R S : Type*} [CommRing R] [CommRing S] (κ : R →+* S)
    {a b : ℕ} (M : Matrix (Fin b) (Fin a) R) (N : Matrix (Fin a) (Fin b) R)
    (hMN : M * N = 1) : M.map κ * N.map κ = 1 := by
  simpa only [Matrix.map_mul, Matrix.map_one _ (map_zero κ) (map_one κ)] using
    congrArg (fun A => A.map κ) hMN

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (k n : ℕ)

/-- Pullback of the original split quotient is the literal coefficient-pulled
quotient, via the actual target free-pullback isomorphism. -/
theorem pullbackPresentation_isomorphic
    (M : Matrix (Fin (n-k)) (Fin n) Γ(X, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(X, ⊤)) (hMN : M * N = 1) :
    (pullbackPresentation f (presentation X k n M N hMN)).Isomorphic
      (presentation Y k n (M.map f.appTop.hom) (N.map f.appTop.hom)
        (rightInverse_map f.appTop.hom M N hMN)) := by
  refine ⟨pullbackFreeIso f (n-k), ?_⟩
  change ((pullbackFreeIso f n).inv ≫ (Scheme.Modules.pullback f).map (ofMatrix M)) ≫
    (pullbackFreeIso f (n-k)).hom = ofMatrix (M.map f.appTop.hom)
  exact pulledFreeMap_ofMatrix f M

theorem pullbackPresentation_class
    (M : Matrix (Fin (n-k)) (Fin n) Γ(X, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(X, ⊤)) (hMN : M * N = 1) :
    pullbackPointsMap f k n (⟦presentation X k n M N hMN⟧ : Points X k n) =
      ⟦presentation Y k n (M.map f.appTop.hom) (N.map f.appTop.hom)
        (rightInverse_map f.appTop.hom M N hMN)⟧ :=
  Quotient.sound (.rel _ _ (pullbackPresentation_isomorphic f k n M N hMN))

/-- Native representability converts the proved presentation pullback into
an equality of the actual integral classifying morphisms. -/
theorem integralMap_comp
    (M : Matrix (Fin (n-k)) (Fin n) Γ(X, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(X, ⊤)) (hMN : M * N = 1) :
    f ≫ integralMap X k n M N hMN =
      integralMap Y k n (M.map f.appTop.hom) (N.map f.appTop.hom)
        (rightInverse_map f.appTop.hom M N hMN) := by
  apply (schemeRepresentableBy k n).homEquiv.injective
  apply ((functorData k n).objEquiv Y).injective
  rw [(schemeRepresentableBy k n).homEquiv_comp]
  rw [pointsEquiv_map, integralMap_class, integralMap_class]
  exact pullbackPresentation_class f k n M N hMN

variable (B : Type u) [Field B]

/-- The actual classifying morphism over the base field is natural under
every scheme pullback, with the original base map retained. -/
theorem map_comp (p : X ⟶ Spec (.of B))
    (M : Matrix (Fin (n-k)) (Fin n) Γ(X, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(X, ⊤)) (hMN : M * N = 1) :
    f ≫ SplitMatrixGrassmannian.map X k n B p M N hMN =
      SplitMatrixGrassmannian.map Y k n B (f ≫ p)
        (M.map f.appTop.hom) (N.map f.appTop.hom)
        (rightInverse_map f.appTop.hom M N hMN) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map_projection]
  · rw [Category.assoc, map_toIntegral, map_toIntegral]
    exact integralMap_comp f k n M N hMN

/-- The literal represented quotient class of an arbitrary native Grassmannian map. -/
def pointClass {T : Scheme.{u}} (q : T ⟶ GrassmannianCharts.space B k n) : Points T k n :=
  (functorData k n).objEquiv T ((schemeRepresentableBy k n).homEquiv
    (q ≫ GrassmannianCharts.toIntegral B k n))

theorem pointClass_comp (q : X ⟶ GrassmannianCharts.space B k n) :
    pointClass k n B (f ≫ q) = pullbackPointsMap f k n (pointClass k n B q) := by
  change (functorData k n).objEquiv Y ((schemeRepresentableBy k n).homEquiv
    ((f ≫ q) ≫ GrassmannianCharts.toIntegral B k n)) = _
  rw [Category.assoc, (schemeRepresentableBy k n).homEquiv_comp]
  exact pointsEquiv_map f k n _

/-- A proved split-matrix quotient class pulls back to the literal mapped
matrix class.  No classifier-naturality premise is needed. -/
theorem class_comp_of_matrix_class (q : X ⟶ GrassmannianCharts.space B k n)
    (M : Matrix (Fin (n-k)) (Fin n) Γ(X, ⊤))
    (N : Matrix (Fin n) (Fin (n-k)) Γ(X, ⊤)) (hMN : M * N = 1)
    (hq : pointClass k n B q = ⟦presentation X k n M N hMN⟧) :
    pointClass k n B (f ≫ q) =
      ⟦presentation Y k n (M.map f.appTop.hom) (N.map f.appTop.hom)
        (rightInverse_map f.appTop.hom M N hMN)⟧ := by
  rw [pointClass_comp, hq]
  exact pullbackPresentation_class f k n M N hMN

section Spec

variable {R S : Type u} [CommRing R] [CommRing S] (φ : R →+* S)

/-- The actual global-section map of `Spec φ` is the literal coefficient
map under the canonical affine global-section isomorphisms. -/
theorem spec_matrix_map {a b : ℕ} (M : Matrix (Fin b) (Fin a) R) :
    (M.map (Scheme.ΓSpecIso (.of R)).inv.hom).map
        (Spec.map (CommRingCat.ofHom φ)).appTop.hom =
      (M.map φ).map (Scheme.ΓSpecIso (.of S)).inv.hom := by
  ext i j
  change (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of R)).inv (M i j)) =
    (Scheme.ΓSpecIso (.of S)).inv (φ (M i j))
  rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
  rfl

/-- A split ring matrix gives its original quotient presentation on its
actual affine spectrum, through the canonical global coefficient map. -/
def ringPresentation (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    QuotientPresentation (Spec (.of R)) k n :=
  presentation (Spec (.of R)) k n
    (M.map (Scheme.ΓSpecIso (.of R)).inv.hom)
    (N.map (Scheme.ΓSpecIso (.of R)).inv.hom)
    (rightInverse_map (Scheme.ΓSpecIso (.of R)).inv.hom M N hMN)

theorem ringPresentation_matrix (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    toMatrix (ringPresentation k n M N hMN).map =
      M.map (Scheme.ΓSpecIso (.of R)).inv.hom := toMatrix_ofMatrix _

/-- Actual Spec pullback of the original ring-matrix presentation has the
literal mapped ring matrix, not merely an isomorphic abstract quotient. -/
theorem spec_pullbackPresentation_isomorphic
    (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    (pullbackPresentation (Spec.map (CommRingCat.ofHom φ))
      (ringPresentation k n M N hMN)).Isomorphic
      (ringPresentation k n (M.map φ) (N.map φ) (rightInverse_map φ M N hMN)) := by
  refine ⟨pullbackFreeIso (Spec.map (CommRingCat.ofHom φ)) (n-k), ?_⟩
  change pulledFreeMap (Spec.map (CommRingCat.ofHom φ))
    (ofMatrix (M.map (Scheme.ΓSpecIso (.of R)).inv.hom)) =
      ofMatrix ((M.map φ).map (Scheme.ΓSpecIso (.of S)).inv.hom)
  exact (pulledFreeMap_ofMatrix (Spec.map (CommRingCat.ofHom φ))
    (M.map (Scheme.ΓSpecIso (.of R)).inv.hom)).trans
      (congrArg ofMatrix (spec_matrix_map φ M))

theorem spec_pullbackPresentation_class
    (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    pullbackPointsMap (Spec.map (CommRingCat.ofHom φ)) k n
      (⟦ringPresentation k n M N hMN⟧ : Points (Spec (.of R)) k n) =
      ⟦ringPresentation k n (M.map φ) (N.map φ) (rightInverse_map φ M N hMN)⟧ :=
  Quotient.sound (.rel _ _ (spec_pullbackPresentation_isomorphic k n φ M N hMN))

/-- The Spec specialization of the actual split classifying morphism is
the classifier of the literal coefficient-pulled matrix. -/
theorem spec_map_comp (p : Spec (.of R) ⟶ Spec (.of B))
    (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    Spec.map (CommRingCat.ofHom φ) ≫ SplitMatrixGrassmannian.map (Spec (.of R)) k n B p
      (M.map (Scheme.ΓSpecIso (.of R)).inv.hom)
      (N.map (Scheme.ΓSpecIso (.of R)).inv.hom)
      (rightInverse_map (Scheme.ΓSpecIso (.of R)).inv.hom M N hMN) =
    SplitMatrixGrassmannian.map (Spec (.of S)) k n B (Spec.map (CommRingCat.ofHom φ) ≫ p)
      ((M.map φ).map (Scheme.ΓSpecIso (.of S)).inv.hom)
      ((N.map φ).map (Scheme.ΓSpecIso (.of S)).inv.hom)
      (rightInverse_map (Scheme.ΓSpecIso (.of S)).inv.hom (M.map φ) (N.map φ)
        (rightInverse_map φ M N hMN)) := by
  have h := map_comp (Spec.map (CommRingCat.ofHom φ)) k n B p
      (M.map (Scheme.ΓSpecIso (.of R)).inv.hom)
      (N.map (Scheme.ΓSpecIso (.of R)).inv.hom)
      (rightInverse_map (Scheme.ΓSpecIso (.of R)).inv.hom M N hMN)
  have hm := spec_matrix_map φ M
  have hn := spec_matrix_map φ N
  simpa only [hm, hn] using h

/-- An actual affine-family quotient class specializes to the literal
coefficient matrix at every ring-valued point. -/
theorem spec_class_comp_of_matrix_class
    (q : Spec (.of R) ⟶ GrassmannianCharts.space B k n)
    (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1)
    (hq : pointClass k n B q = ⟦ringPresentation k n M N hMN⟧) :
    pointClass k n B (Spec.map (CommRingCat.ofHom φ) ≫ q) =
      ⟦ringPresentation k n (M.map φ) (N.map φ) (rightInverse_map φ M N hMN)⟧ := by
  rw [pointClass_comp, hq]
  exact spec_pullbackPresentation_class k n φ M N hMN

end Spec

section Field

variable {R L : Type u} [CommRing R] [Field L] (φ : R →+* L)

/-- Specializing the proved rectangular right inverse supplies actual
surjectivity of the original specialized field matrix. -/
theorem mapped_mulVec_surjective (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1) :
    Function.Surjective (Matrix.mulVec (M.map φ)) :=
  Matrix.mulVec_surjective_iff_exists_right_inverse.mpr ⟨N.map φ, rightInverse_map φ M N hMN⟩

/-- The literal field presentation agrees with any actual splitting of its
matrix; the chosen right inverse is absent from the quotient map itself. -/
theorem ringPresentation_eq_fieldPresentation
    (M : Matrix (Fin (n-k)) (Fin n) L)
    (N : Matrix (Fin n) (Fin (n-k)) L) (hMN : M * N = 1)
    (hM : Function.Surjective (Matrix.mulVec M)) :
    ringPresentation k n M N hMN = fieldPresentation k n L M hM := rfl

/-- Every actual field-valued point of a split-matrix affine family has the
original represented field-matrix quotient class. -/
theorem spec_class_comp_fieldPresentation
    (q : Spec (.of R) ⟶ GrassmannianCharts.space B k n)
    (M : Matrix (Fin (n-k)) (Fin n) R)
    (N : Matrix (Fin n) (Fin (n-k)) R) (hMN : M * N = 1)
    (hq : pointClass k n B q = ⟦ringPresentation k n M N hMN⟧) :
    pointClass k n B (Spec.map (CommRingCat.ofHom φ) ≫ q) =
      ⟦fieldPresentation k n L (M.map φ) (mapped_mulVec_surjective k n φ M N hMN)⟧ := by
  exact spec_class_comp_of_matrix_class k n B φ q M N hMN hq

end Field

end M9Native.SplitMatrixGrassmannianNaturality
