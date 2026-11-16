module

public import M9StacksIntegration.LagrangianKernelProjectiveComparison
public import M9StacksIntegration.LagrangianKernelFivePullback
public import M9StacksIntegration.ProjectiveQuadricLinearPullback
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections

/-!
# Actual projective factorization of a surjective linear system

The graded quotient is the symmetric-algebra map in the two original
bases. Its scalar and generator formulas determine the actual projective
triangle on genuine affine line frames. Section generation of the smaller
system is derived from the literal linear expansion of the larger one.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators
open Stacks.AlgebraicGeometry.ProjPolyChart Stacks.AlgebraicGeometry.ProjBaseChange
open Stacks.ProjectiveSpaceChartRatio

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  SheafOfModules.unit PresheafOfModules.unit

namespace M9Native.ProjectiveLinearSystemFactor

open LagrangianMatrixChart LagrangianPluckerQuotient LagrangianSectionGeneration

variable (K : Type u) [Field K] {U V : Type u} [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] {n m : ℕ}
    (bU : Basis (Fin (n + 1)) K U) (bV : Basis (Fin (m + 1)) K V)
    (F : U →ₗ[K] V)

/-- The actual homogeneous quotient in the two specified coordinate bases. -/
def gradedHom : polyGrading K n →+*ᵍ polyGrading K m :=
  (SymPow.gradedMvPolynomialHom bV).comp
    ((SymPow.gradedSymAlgMap F).comp (SymPow.gradedMvPolynomialInv bU))

theorem gradedHom_surjective (hF : Function.Surjective F) :
    Function.Surjective (gradedHom K bU bV F) :=
  (SymmetricAlgebra.equivMvPolynomial bV).surjective.comp
    ((SymPow.symAlgMap_surjective F hF).comp
      (SymmetricAlgebra.equivMvPolynomial bU).symm.surjective)

theorem gradedHom_C (c : K) :
    gradedHom K bU bV F (MvPolynomial.C c) = MvPolynomial.C c := by
  change SymmetricAlgebra.equivMvPolynomial bV
    (SymPow.symAlgMap F ((SymmetricAlgebra.equivMvPolynomial bU).symm
      (algebraMap K (MvPolynomial (Fin (n+1)) K) c))) =
    algebraMap K (MvPolynomial (Fin (m+1)) K) c
  rw [AlgEquiv.commutes, AlgHom.commutes, AlgEquiv.commutes]

theorem gradedHom_X (j : Fin (n+1)) :
    gradedHom K bU bV F (MvPolynomial.X j) =
      ∑ i : Fin (m+1), MvPolynomial.C (bV.repr (F (bU j)) i) * MvPolynomial.X i := by
  change SymmetricAlgebra.equivMvPolynomial bV
    (SymPow.symAlgMap F ((SymmetricAlgebra.equivMvPolynomial bU).symm (MvPolynomial.X j))) = _
  have hu : (SymmetricAlgebra.equivMvPolynomial bU).symm (MvPolynomial.X j) =
      SymmetricAlgebra.ι K U (bU j) := by
    apply (SymmetricAlgebra.equivMvPolynomial bU).injective
    rw [AlgEquiv.apply_symm_apply, SymmetricAlgebra.equivMvPolynomial_ι_apply]
  rw [hu, SymPow.symAlgMap_ι]
  have hv := congrArg (fun v => SymmetricAlgebra.equivMvPolynomial bV
      (SymmetricAlgebra.ι K V v)) (bV.sum_repr (F (bU j)))
  simpa only [map_sum, map_smul, SymmetricAlgebra.equivMvPolynomial_ι_apply,
    Algebra.smul_def, map_mul, AlgEquiv.commutes,
    SymmetricAlgebra.equivMvPolynomial_ι_apply, MvPolynomial.algebraMap_eq] using hv.symm

def polynomialEmbedding (hF : Function.Surjective F) : AlgebraicGeometry.Proj (polyGrading K m) ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  Proj.map (gradedHom K bU bV F)
    (Proj.irrelevant_le_map_of_surjective _ (gradedHom_surjective K bU bV F hF))

instance polynomialEmbedding_closed (hF : Function.Surjective F) :
    IsClosedImmersion (polynomialEmbedding K bU bV F hF) :=
  Proj.isClosedImmersion_map_of_surjective' _ (gradedHom_surjective K bU bV F hF)

theorem polynomialEmbedding_over (hF : Function.Surjective F) :
    polynomialEmbedding K bU bV F hF ≫ projToSpecCoeff K n = projToSpecCoeff K m := by
  have h0 : (gradedHom K bU bV F).gradedZeroRingHom.comp
      (algebraMap K (polyGrading K n 0)) = algebraMap K (polyGrading K m 0) := by
    apply RingHom.ext
    intro c
    apply Subtype.ext
    exact gradedHom_C K bU bV F c
  dsimp only [polynomialEmbedding]
  rw [projToSpecCoeff, projToSpecCoeff,
    ProjectiveQuadricLinearPullback.coefficientZeroHom_eq,
    ProjectiveQuadricLinearPullback.coefficientZeroHom_eq,
    ← Category.assoc, Proj.map_toSpecZero, Category.assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, h0]

def embedding (hF : Function.Surjective F) :
    projectiveSpaceOver m (Spec (.of K)) ⟶ projectiveSpaceOver n (Spec (.of K)) :=
  (polynomialComparison K m).iso.hom ≫ polynomialEmbedding K bU bV F hF ≫
    (polynomialComparison K n).iso.inv

instance embedding_closed (hF : Function.Surjective F) :
    IsClosedImmersion (embedding K bU bV F hF) := by
  dsimp [embedding]
  infer_instance

private theorem evaluation_triangle_ring {R : Type u} [CommRing R] (κ : K →+* R)
    (sU : Fin (n+1) → R) (sV : Fin (m+1) → R)
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), κ (bV.repr (F (bU j)) i) * sV i) :
    (MvPolynomial.eval₂Hom κ sV).comp (gradedHom K bU bV F).toRingHom =
      MvPolynomial.eval₂Hom κ sU := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom, gradedHom_C, MvPolynomial.eval₂Hom_C]
  · intro j
    simp only [RingHom.comp_apply, GradedRingHom.coe_toRingHom]
    rw [gradedHom_X]
    have hs : (MvPolynomial.eval₂Hom κ sV)
        (∑ i : Fin (m+1), MvPolynomial.C (bV.repr (F (bU j)) i) * MvPolynomial.X i) =
        ∑ i : Fin (m+1), (MvPolynomial.eval₂Hom κ sV)
          (MvPolynomial.C (bV.repr (F (bU j)) i) * MvPolynomial.X i) := by
      with_unfolding_all exact map_sum (MvPolynomial.eval₂Hom κ sV).toAddMonoidHom _ _
    rw [hs]
    simp only [map_mul, MvPolynomial.eval₂Hom_C, MvPolynomial.eval₂Hom_X']
    exact (hrel j).symm

theorem evaluation_triangle {T : Scheme.{u}} (f : T ⟶ Spec (.of K))
    (sU : Fin (n+1) → Γ(T, ⊤)) (sV : Fin (m+1) → Γ(T, ⊤))
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) * sV i) :
    (MvPolynomial.eval₂Hom (baseRingHom f) sV).comp (gradedHom K bU bV F).toRingHom =
      MvPolynomial.eval₂Hom (baseRingHom f) sU :=
  evaluation_triangle_ring K bU bV F (baseRingHom f) sU sV hrel

theorem functions_triangle (hF : Function.Surjective F) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of K)) (sU : Fin (n+1) → Γ(T, ⊤))
    (hU : Ideal.span (Set.range sU) = ⊤) (sV : Fin (m+1) → Γ(T, ⊤))
    (hV : Ideal.span (Set.range sV) = ⊤)
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) * sV i) :
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sV hV f ≫
        embedding K bU bV F hF =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sU hU f := by
  have he := evaluation_triangle K bU bV F f sU sV hrel
  have hComp : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
      ((MvPolynomial.eval₂Hom (baseRingHom f) sV).comp (gradedHom K bU bV F).toRingHom) = ⊤ := by
    rw [he]
    exact map_irrelevant_eval₂Hom_eq_top (baseRingHom f) sU hU
  have hp : Proj.fromOfGlobalSections (polyGrading K m)
      (MvPolynomial.eval₂Hom (baseRingHom f) sV)
      (map_irrelevant_eval₂Hom_eq_top (baseRingHom f) sV hV) ≫
        polynomialEmbedding K bU bV F hF =
      Proj.fromOfGlobalSections (polyGrading K n) (MvPolynomial.eval₂Hom (baseRingHom f) sU)
        (map_irrelevant_eval₂Hom_eq_top (baseRingHom f) sU hU) := by
    rw [polynomialEmbedding, Proj.fromOfGlobalSections_comp_map _ _ _ _ hComp]
    exact Proj.fromOfGlobalSections_congr he _ _
  rw [← LagrangianProjectiveSections.fromEvaluation_comp_comparison_inv f sV hV,
    ← LagrangianProjectiveSections.fromEvaluation_comp_comparison_inv f sU hU, embedding]
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
    congrArg (fun t => t ≫ (polynomialComparison K n).iso.inv) hp

theorem framed_triangle (hF : Function.Surjective F) {T : Scheme.{u}}
    (f : T ⟶ Spec (.of K)) {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
    (sU : Fin (n+1) → Γ(L, ⊤)) (hU : Stacks.ProjectiveFromSections.GeneratesStalks sU)
    (sV : Fin (m+1) → Γ(L, ⊤)) (hV : Stacks.ProjectiveFromSections.GeneratesStalks sV)
    (e : L ≅ ProjectiveSectionFunctions.UnitLine T)
    (hspanU : Ideal.span (Set.range (fun j => (show Γ(T, ⊤) from e.hom.app ⊤ (sU j)))) = ⊤)
    (hspanV : Ideal.span (Set.range (fun i => (show Γ(T, ⊤) from e.hom.app ⊤ (sV i)))) = ⊤)
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) • sV i) :
    Stacks.ProjectiveFromSections.toProjectiveSpaceOver sV hV f ≫
        embedding K bU bV F hF =
      Stacks.ProjectiveFromSections.toProjectiveSpaceOver sU hU f := by
  rw [LagrangianKernelProjectiveComparison.toProjectiveSpaceOver_framed sU hU e f hspanU,
    LagrangianKernelProjectiveComparison.toProjectiveSpaceOver_framed sV hV e f hspanV]
  apply functions_triangle K bU bV F hF f _ hspanU _ hspanV
  intro j
  have h := congrArg (fun s => e.hom.app ⊤ s) (hrel j)
  simpa only [map_sum, Scheme.Modules.Hom.app_smul, smul_eq_mul] using h

def coefficientSections {T : Scheme.{u}} (f : T ⟶ Spec (.of K))
    (j : Fin (n+1)) : Γ(freeOn T (m+1), ⊤) :=
  ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) • freeBasisSection T (m+1) i

def coefficientMap {T : Scheme.{u}} (f : T ⟶ Spec (.of K)) :
    freeOn T (n+1) ⟶ freeOn T (m+1) :=
  sectionMap T (freeOn T (m+1)) (coefficientSections K bU bV F f)

/-- Literal section expansion gives an actual factorization of the
original free-section morphism. -/
theorem sectionMap_factor {T : Scheme.{u}} (f : T ⟶ Spec (.of K)) {L : T.Modules}
    (sU : Fin (n+1) → Γ(L, ⊤)) (sV : Fin (m+1) → Γ(L, ⊤))
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) • sV i) :
    sectionMap T L sU = coefficientMap K bU bV F f ≫ sectionMap T L sV := by
  have hv : (fun j => (sectionMap T L sV).app ⊤
      (coefficientSections K bU bV F f j)) = sU := by
    funext j
    simp only [coefficientSections, map_sum, Scheme.Modules.Hom.app_smul, sectionMap_top_basis]
    exact (hrel j).symm
  symm
  exact (MukaiPrimitiveCanonicalEvaluation.sectionMap_postcomp
    (coefficientSections K bU bV F f) (sectionMap T L sV)).trans
      (congrArg (sectionMap T L) hv)

/-- The smaller actual section system generates because the larger
original system generates and factors through it. -/
theorem generatesStalks_of_expansion {T : Scheme.{u}} (f : T ⟶ Spec (.of K))
    {L : T.Modules} [Stacks.Ample.IsInvertibleModule T L]
    (sU : Fin (n+1) → Γ(L, ⊤)) (hU : Stacks.ProjectiveFromSections.GeneratesStalks sU)
    (sV : Fin (m+1) → Γ(L, ⊤))
    (hrel : ∀ j, sU j = ∑ i : Fin (m+1), baseRingHom f (bV.repr (F (bU j)) i) • sV i) :
    Stacks.ProjectiveFromSections.GeneratesStalks sV := by
  let : Epi (sectionMap T L sU) := LagrangianPluckerGeneration.sectionMap_epi_of_generatesStalks sU hU
  have hcomp : Epi (coefficientMap K bU bV F f ≫ sectionMap T L sV) :=
    (sectionMap_factor K bU bV F f sU sV hrel) ▸ inferInstance
  let : Epi (coefficientMap K bU bV F f ≫ sectionMap T L sV) := hcomp
  let : Epi (sectionMap T L sV) := epi_of_epi (coefficientMap K bU bV F f) _
  exact generatesStalks_of_sectionMap_epi T L sV inferInstance

end M9Native.ProjectiveLinearSystemFactor
