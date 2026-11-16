module

public import M9StacksIntegration.MukaiProjSectionsNaturality
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinesAvoidingSubvariety
public import StacksFrontier.AlgebraicGeometry.SectionsToProjectiveSpace.Basic

/-! # The actual value of a basis-coordinate projective morphism -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart

universe u

namespace M9Native.MukaiProjectiveEvaluationPoint

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]

abbrev grading := fun n : ℕ => SymPow.symmetricPower n K V

def scalarSections : K →+* Γ(Spec (.of K), ⊤) := (Scheme.ΓSpecIso (.of K)).inv.hom

def evaluationSections (φ : Module.Dual K V) : SymmetricAlgebra K V →+* Γ(Spec (.of K), ⊤) :=
  (scalarSections K).comp (SymmetricAlgebra.lift φ).toRingHom

@[simp] theorem evaluationSections_ι (φ : Module.Dual K V) (v : V) :
    evaluationSections K V φ (SymmetricAlgebra.ι K V v) = scalarSections K (φ v) := by
  simp [evaluationSections]

theorem map_irrelevant_evaluationSections (φ : Module.Dual K V) (v₀ : V) (hv₀ : φ v₀ = 1) :
    (HomogeneousIdeal.irrelevant (grading K V)).toIdeal.map (evaluationSections K V φ) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (evaluationSections K V φ)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading K V) Nat.one_pos
      (ι_mem_symmetricPower_one K V v₀))
  rw [evaluationSections_ι,hv₀,(scalarSections K).map_one] at h
  exact h

def evaluationMorphism (φ : Module.Dual K V) (v₀ : V) (hv₀ : φ v₀ = 1) :
    Spec (.of K) ⟶ projectiveSpaceOfModule K V :=
  Proj.fromOfGlobalSections (grading K V) (evaluationSections K V φ)
    (map_irrelevant_evaluationSections K V φ v₀ hv₀)

/-- This proves the actual native point value; no coordinate-point equality is assumed. -/
theorem evaluationMorphism_base (φ : Module.Dual K V) (hφ : φ ≠ 0) (v₀ : V) (hv₀ : φ v₀ = 1)
    (x : Spec (.of K)) :
    evaluationMorphism K V φ v₀ hv₀ x = linearFunctionalPoint K V φ hφ := by
  have hsub : LinearMap.ker φ ≤ pointSubmodule K V (evaluationMorphism K V φ v₀ hv₀ x) := by
    intro v hv
    change SymmetricAlgebra.ι K V v ∈
      (evaluationMorphism K V φ v₀ hv₀ x).asHomogeneousIdeal
    by_contra hn
    have hx : x ∈ evaluationMorphism K V φ v₀ hv₀ ⁻¹ᵁ
        Proj.basicOpen (grading K V) (SymmetricAlgebra.ι K V v) := hn
    rw [evaluationMorphism,Proj.fromOfGlobalSections_preimage_basicOpen (grading K V)
      (evaluationSections K V φ) (map_irrelevant_evaluationSections K V φ v₀ hv₀) Nat.one_pos
      (ι_mem_symmetricPower_one K V v),evaluationSections_ι,show φ v = 0 from hv,map_zero,
      Scheme.basicOpen_zero] at hx
    exact hx
  have hmem := (mem_linearSubspace_iff K V (LinearMap.ker φ) _).mpr hsub
  rwa [linearSubspace_ker K V φ hφ,Set.mem_singleton_iff] at hmem

theorem evaluationMorphism_toSpec (φ : Module.Dual K V) (v₀ : V) (hv₀ : φ v₀ = 1) :
    evaluationMorphism K V φ v₀ hv₀ ≫ projectiveSpaceOfModuleToSpec K V = 𝟙 _ := by
  rw [evaluationMorphism,projectiveSpaceOfModuleToSpec,← Category.assoc,
    Proj.fromOfGlobalSections_toSpecZero,Category.assoc,← Spec.map_comp,← CommRingCat.ofHom_comp]
  have hc : ((evaluationSections K V φ).comp
      (algebraMap (SymPow.symmetricPower 0 K V) (SymmetricAlgebra K V))).comp
      (algebraMap K (SymPow.symmetricPower 0 K V)) = scalarSections K := by
    ext c
    change scalarSections K ((SymmetricAlgebra.lift φ) (algebraMap K (SymmetricAlgebra K V) c)) =
      scalarSections K c
    rw [AlgHom.commutes]
    rfl
  rw [hc]
  exact toSpecΓ_SpecMap_ΓSpecIso_inv (.of K)

section Basis

variable {n : ℕ} (b : Module.Basis (Fin (n+1)) K V)

def polynomialSections (w : Fin (n+1) → K) : MvPolynomial (Fin (n+1)) K →+* Γ(Spec (.of K), ⊤) :=
  (scalarSections K).comp (MvPolynomial.eval w)

theorem map_irrelevant_polynomialSections (w : Fin (n+1) → K) (i : Fin (n+1)) (hi : w i = 1) :
    (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map (polynomialSections K w) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h := Ideal.mem_map_of_mem (polynomialSections K w)
    (HomogeneousIdeal.mem_irrelevant_of_mem (polyGrading K n) Nat.one_pos (X_mem_one K n i))
  have he : polynomialSections K w (MvPolynomial.X i) = scalarSections K (w i) := by
    rw [polynomialSections,RingHom.comp_apply,MvPolynomial.eval_X]
  rw [he,hi,(scalarSections K).map_one] at h
  exact h

def polynomialMorphism (w : Fin (n+1) → K) (i : Fin (n+1)) (hi : w i = 1) :
    Spec (.of K) ⟶ Proj (polyGrading K n) :=
  Proj.fromOfGlobalSections (polyGrading K n) (polynomialSections K w)
    (map_irrelevant_polynomialSections K w i hi)

theorem evaluationSections_comp_basis (φ : Module.Dual K V) :
    (evaluationSections K V φ).comp (SymPow.gradedMvPolynomialInv b).toRingHom =
      polynomialSections K (fun i => φ (b i)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [evaluationSections,polynomialSections,RingHom.comp_apply,MvPolynomial.eval_C]
    change scalarSections K ((SymmetricAlgebra.lift φ)
      ((SymmetricAlgebra.equivMvPolynomial b).symm (algebraMap K (MvPolynomial (Fin (n+1)) K) c))) =
        scalarSections K c
    rw [AlgEquiv.commutes,AlgHom.commutes]
    rfl
  · intro i
    simp [evaluationSections,polynomialSections,SymPow.gradedMvPolynomialInv_apply,
      SymmetricAlgebra.equivMvPolynomial_symm_X]

private theorem polynomialProj_congr (f g : MvPolynomial (Fin (n+1)) K →+* Γ(Spec (.of K), ⊤))
    (hf : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map g = ⊤) (hfg : f = g) :
    Proj.fromOfGlobalSections (polyGrading K n) f hf =
      Proj.fromOfGlobalSections (polyGrading K n) g hg := by
  subst g
  rfl

/-- The actual symmetric-algebra morphism reads as the actual polynomial coordinate morphism. -/
theorem evaluationMorphism_polynomial (φ : Module.Dual K V) (i : Fin (n+1))
    (hi : φ (b i) = 1) :
    evaluationMorphism K V φ (b i) hi ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom =
      polynomialMorphism K (fun j => φ (b j)) i hi := by
  have hcomp : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
      ((evaluationSections K V φ).comp (SymPow.gradedMvPolynomialInv b).toRingHom) = ⊤ := by
    rw [evaluationSections_comp_basis]
    exact map_irrelevant_polynomialSections K _ i hi
  have h := MukaiProjSectionsNaturality.fromOfGlobalSections_comp_map
    (polyGrading K n) (grading K V) (SymPow.gradedMvPolynomialInv b) (evaluationSections K V φ)
    (irrelevant_le_map_gradedMvPolynomialInv b)
    (map_irrelevant_evaluationSections K V φ (b i) hi) hcomp
  exact h.trans (polynomialProj_congr K _ _ hcomp
    (map_irrelevant_polynomialSections K _ i hi) (evaluationSections_comp_basis K V b φ))

/-- The exact basis isomorphism, with the field polynomial model made explicit. -/
theorem basis_inverse_polynomial :
    (basisProjectiveSpaceIso b).inv ≫ (polynomialComparison K n).iso.hom =
      (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom := by
  change ((projectiveSpaceOfModuleIsoProjMvPolynomial b).hom ≫ (polynomialComparison K n).iso.inv) ≫
    (polynomialComparison K n).iso.hom = _
  simp only [Category.assoc,Iso.inv_hom_id,Category.comp_id]

end Basis

end M9Native.MukaiProjectiveEvaluationPoint
