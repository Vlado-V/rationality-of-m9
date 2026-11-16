module

public import M9StacksIntegration.NativeProjectiveLinear
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.UnitRescale
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.GradedNaturality
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.HomogeneousRescale

/-! The genuine native projective morphism of a unimodular vector over a ring,
with actual pullback, scaling, and linear-coordinate formulas. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Matrix MvPolynomial
open Stacks.AlgebraicGeometry.ProjPolyChart
open scoped BigOperators

universe u

namespace M9Native.NativeProjectiveVector

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K R S : Type u} [CommRing K] [CommRing R] [CommRing S] {n : ℕ}

theorem span_mulVec_le (M : Matrix (Fin (n+1)) (Fin (n+1)) R) (v : Fin (n+1) → R) :
    Ideal.span (Set.range (M *ᵥ v)) ≤ Ideal.span (Set.range v) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (∑ j, M i j * v j) ∈ Ideal.span (Set.range v)
  apply Ideal.sum_mem
  intro j _
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

theorem span_mulVec_eq (M N : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hNM : N*M = 1) (v : Fin (n+1) → R) :
    Ideal.span (Set.range (M *ᵥ v)) = Ideal.span (Set.range v) := by
  apply le_antisymm (span_mulVec_le M v)
  have h := span_mulVec_le N (M *ᵥ v)
  rwa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] at h

theorem span_map_eq_top (φ : R →+* S) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range (φ ∘ v)) = ⊤ := by
  rw [Set.range_comp, ← Ideal.map_span, hv, Ideal.map_top]

theorem span_unit_mul_eq (u : Rˣ) (v : Fin (n+1) → R) :
    Ideal.span (Set.range fun i => (u : R)*v i) = Ideal.span (Set.range v) := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    have hi : v i = (↑u⁻¹ : R) * ((u : R)*v i) := by
      rw [← mul_assoc, Units.inv_mul, one_mul]
    rw [hi]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

def vectorMap (f : K →+* R) (v : Fin (n+1) → R) : MvPolynomial (Fin (n+1)) K →+* R :=
  MvPolynomial.eval₂Hom f v

theorem vectorMap_irrelevant (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map (vectorMap f v) = ⊤ := by
  apply le_antisymm le_top
  rw [← hv]
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  have hi := HomogeneousIdeal.mem_irrelevant_of_mem (polyGrading K n) Nat.one_pos
    (X_mem_one K n i)
  simpa [vectorMap] using Ideal.mem_map_of_mem (vectorMap f v) hi

def globalVectorMap (f : K →+* R) (v : Fin (n+1) → R) :
    MvPolynomial (Fin (n+1)) K →+* Γ(Spec (.of R), ⊤) :=
  (Scheme.ΓSpecIso (.of R)).inv.hom.comp (vectorMap f v)

theorem globalVectorMap_irrelevant (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map (globalVectorMap f v) = ⊤ := by
  rw [globalVectorMap, ← Ideal.map_map, vectorMap_irrelevant f v hv, Ideal.map_top]

/-- The literal vector defines an actual native `Proj` morphism. -/
def point (f : K →+* R) (v : Fin (n+1) → R) (hv : Ideal.span (Set.range v) = ⊤) :
    Spec (.of R) ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  Proj.fromOfGlobalSections (polyGrading K n) (globalVectorMap f v)
    (globalVectorMap_irrelevant f v hv)

theorem point_congr (f : K →+* R) {v w : Fin (n+1) → R} (h : v = w)
    (hv : Ideal.span (Set.range v) = ⊤) (hw : Ideal.span (Set.range w) = ⊤) :
    point f v hv = point f w hw := by
  cases h
  rfl

def onScheme (X : Scheme.{u}) (f : K →+* Γ(X, ⊤)) (v : Fin (n+1) → Γ(X, ⊤))
    (hv : Ideal.span (Set.range v) = ⊤) : X ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  Proj.fromOfGlobalSections (polyGrading K n) (vectorMap f v) (vectorMap_irrelevant f v hv)

theorem point_eq_onScheme (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    point f v hv = onScheme (Spec (.of R))
      ((Scheme.ΓSpecIso (.of R)).inv.hom.comp f)
      ((Scheme.ΓSpecIso (.of R)).inv.hom ∘ v)
      (span_map_eq_top (Scheme.ΓSpecIso (.of R)).inv.hom v hv) := by
  have h : globalVectorMap f v = vectorMap ((Scheme.ΓSpecIso (.of R)).inv.hom.comp f)
      ((Scheme.ΓSpecIso (.of R)).inv.hom ∘ v) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [globalVectorMap, vectorMap]
  exact Proj.fromOfGlobalSections_congr h _ _

theorem onScheme_map {X Y : Scheme.{u}} (g : Y ⟶ X) (f : K →+* Γ(X, ⊤))
    (v : Fin (n+1) → Γ(X, ⊤)) (hv : Ideal.span (Set.range v) = ⊤) :
    g ≫ onScheme X f v hv =
      onScheme Y (g.appTop.hom.comp f) (g.appTop.hom ∘ v)
        (span_map_eq_top g.appTop.hom v hv) := by
  have heq : g.appTop.hom.comp (vectorMap f v) =
      vectorMap (g.appTop.hom.comp f) (g.appTop.hom ∘ v) := by
    apply MvPolynomial.ringHom_ext <;> intro i <;> simp [vectorMap]
  exact (Proj.comp_fromOfGlobalSections (polyGrading K n) _ _ _
    (by rw [heq]; exact vectorMap_irrelevant _ _ (span_map_eq_top g.appTop.hom v hv))).trans
      (Proj.fromOfGlobalSections_congr heq _ _)

theorem onScheme_scale (X : Scheme.{u}) (f : K →+* Γ(X, ⊤))
    (v : Fin (n+1) → Γ(X, ⊤)) (hv : Ideal.span (Set.range v) = ⊤)
    (u : Γ(X, ⊤)ˣ) (huv : Ideal.span (Set.range fun i => (u : Γ(X, ⊤))*v i) = ⊤) :
    onScheme X f (fun i => (u : Γ(X, ⊤))*v i) huv = onScheme X f v hv := by
  apply Eq.symm
  apply Proj.fromOfGlobalSections_congr_unit (polyGrading K n)
    (vectorMap f v) (vectorMap f (fun i => (u : Γ(X, ⊤))*v i)) u
  intro d p hp
  exact ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).eval₂Hom_const_mul f v u

theorem onScheme_linear (X : Scheme.{u}) (f : K →+* Γ(X, ⊤))
    (v : Fin (n+1) → Γ(X, ⊤)) (hv : Ideal.span (Set.range v) = ⊤)
    (B : Matrix.GeneralLinearGroup (Fin (n+1)) K)
    (hBv : Ideal.span (Set.range ((B.val.map f) *ᵥ v)) = ⊤) :
    onScheme X f ((B.val.map f) *ᵥ v) hBv =
      onScheme X f v hv ≫ (NativeProjectiveLinear.projectiveLinear K n B).hom := by
  have heq : (vectorMap f v).comp (NativeProjectiveLinear.substitution K n B.val).toRingHom =
      vectorMap f ((B.val.map f) *ᵥ v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [vectorMap]
    · intro i
      simp [vectorMap, NativeProjectiveLinear.substitution_X, Matrix.mulVec, dotProduct]
  exact ((Proj.fromOfGlobalSections_comp_map
      (NativeProjectiveLinear.substitution K n B.val)
      (NativeProjectiveLinear.substitution_irrelevant_le K n B)
      (vectorMap f v) (vectorMap_irrelevant f v hv)
      (by rw [heq]; exact vectorMap_irrelevant f _ hBv)).trans
    (Proj.fromOfGlobalSections_congr heq _ _)).symm

theorem spec_appTop (φ : R →+* S) (r : R) :
    (Spec.map (CommRingCat.ofHom φ)).appTop ((Scheme.ΓSpecIso (.of R)).inv r) =
      (Scheme.ΓSpecIso (.of S)).inv (φ r) := by
  have h := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
  exact (congrArg (fun g => g r) (congrArg CommRingCat.Hom.hom h)).symm

theorem point_map (φ : R →+* S) (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) :
    Spec.map (CommRingCat.ofHom φ) ≫ point f v hv =
      point (φ.comp f) (φ ∘ v) (span_map_eq_top φ v hv) := by
  have heq : (Spec.map (CommRingCat.ofHom φ)).appTop.hom.comp (globalVectorMap f v) =
      globalVectorMap (φ.comp f) (φ ∘ v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simpa [globalVectorMap, vectorMap] using spec_appTop φ (f c)
    · intro i
      simpa [globalVectorMap, vectorMap] using spec_appTop φ (v i)
  exact (Proj.comp_fromOfGlobalSections (polyGrading K n) _ _ _
    (heq ▸ globalVectorMap_irrelevant (φ.comp f) (φ ∘ v) (span_map_eq_top φ v hv))).trans
      (Proj.fromOfGlobalSections_congr heq _ _)

theorem point_scale (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) (u : Rˣ)
    (huv : Ideal.span (Set.range fun i => (u : R)*v i) = ⊤) :
    point f (fun i => (u : R)*v i) huv = point f v hv := by
  apply Eq.symm
  apply Proj.fromOfGlobalSections_congr_unit (polyGrading K n)
    (globalVectorMap f v) (globalVectorMap f (fun i => (u : R)*v i))
    (Units.map (Scheme.ΓSpecIso (.of R)).inv.hom.toMonoidHom u)
  intro d p hp
  change (Scheme.ΓSpecIso (.of R)).inv ((MvPolynomial.eval₂Hom f (fun i => (u : R)*v i)) p) = _
  rw [((MvPolynomial.mem_homogeneousSubmodule _ _).mp hp).eval₂Hom_const_mul]
  simp only [map_mul, map_pow, Units.coe_map]
  rfl

theorem point_linear (f : K →+* R) (v : Fin (n+1) → R)
    (hv : Ideal.span (Set.range v) = ⊤) (B : Matrix.GeneralLinearGroup (Fin (n+1)) K)
    (hBv : Ideal.span (Set.range ((B.val.map f) *ᵥ v)) = ⊤) :
    point f ((B.val.map f) *ᵥ v) hBv =
      point f v hv ≫ (NativeProjectiveLinear.projectiveLinear K n B).hom := by
  have heq : (globalVectorMap f v).comp
      (NativeProjectiveLinear.substitution K n B.val).toRingHom =
      globalVectorMap f ((B.val.map f) *ᵥ v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [globalVectorMap, vectorMap]
    · intro i
      simp [globalVectorMap, vectorMap, NativeProjectiveLinear.substitution_X,
        Matrix.mulVec, dotProduct]
  exact ((Proj.fromOfGlobalSections_comp_map
      (NativeProjectiveLinear.substitution K n B.val)
      (NativeProjectiveLinear.substitution_irrelevant_le K n B)
      (globalVectorMap f v) (globalVectorMap_irrelevant f v hv)
      (heq ▸ globalVectorMap_irrelevant f _ hBv)).trans
    (Proj.fromOfGlobalSections_congr heq _ _)).symm

end M9Native.NativeProjectiveVector
