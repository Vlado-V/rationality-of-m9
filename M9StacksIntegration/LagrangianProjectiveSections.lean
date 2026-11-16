module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceCoordinates
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceChartRatio.PolynomialModel
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.LinearAction
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceDimension
public import StacksFrontier.AlgebraicGeometry.Limits.ProjGradedSurjection01N0

/-! Canonical coordinate identities for the actual projective-module model,
used by the primitive LG Plucker factorization. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.ProjectiveSpaceChartRatio
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

namespace M9Native.LagrangianProjectiveSections

variable {K V : Type u} [CommRing K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Module.Basis (Fin (n+1)) K V)

theorem modulePolynomialIso_inv :
    (projectiveSpaceOfModuleIsoProjMvPolynomial b).inv=
      Proj.map (SymPow.gradedMvPolynomialHom b) (irrelevant_le_map_gradedMvPolynomialHom b) := by
  apply (cancel_mono (projectiveSpaceOfModuleIsoProjMvPolynomial b).hom).1
  rw [Iso.inv_hom_id,projectiveSpaceOfModuleIsoProjMvPolynomial_hom,← Proj.map_comp]
  simp only [SymPow.gradedMvPolynomialHom_comp_inv,Proj.map_id]

/-- The coordinate basis isomorphism uses the actual coefficient-base-change
comparison and the actual symmetric-algebra coordinate homomorphism. -/
theorem basisProjectiveSpaceIso_hom :
    (basisProjectiveSpaceIso b).hom=(polynomialComparison K n).iso.hom ≫
      Proj.map (SymPow.gradedMvPolynomialHom b) (irrelevant_le_map_gradedMvPolynomialHom b) := by
  change (polynomialComparison K n).iso.hom ≫ (projectiveSpaceOfModuleIsoProjMvPolynomial b).inv=_
  rw [modulePolynomialIso_inv]


end M9Native.LagrangianProjectiveSections

namespace M9Native.LagrangianProjectiveSections

variable {K : Type u} [CommRing K] {n : ℕ} {T : Scheme.{u}}

/-- The actual field-polynomial evaluation morphism and the actual
base-change projective morphism agree through the native comparison. -/
theorem fromEvaluation_comp_comparison_inv (f : T ⟶ Spec (.of K))
    (s : Fin (n+1) → Γ(T,⊤)) (hs : Ideal.span (Set.range s)=⊤) :
    Proj.fromOfGlobalSections (polyGrading K n) (MvPolynomial.eval₂Hom (baseRingHom f) s)
        (map_irrelevant_eval₂Hom_eq_top (baseRingHom f) s hs) ≫
      (polynomialComparison K n).iso.inv=
        Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver s hs f := by
  have hb : (polynomialComparison K n).iso.inv ≫ pullback.fst _ _=projToSpecCoeff K n := by
    apply (cancel_epi (polynomialComparison K n).iso.hom).1
    rw [Iso.hom_inv_id_assoc,polynomialComparison_iso_hom_comp_projToSpecCoeff]
  have hi : (polynomialComparison K n).iso.inv ≫ pullback.snd _ _=
      coordinateProjMap K n (integralGradedHom K n) (mapDomain_integralGradedHom_eq_top K n) := by
    apply (cancel_epi (polynomialComparison K n).iso.hom).1
    rw [Iso.hom_inv_id_assoc,polynomialComparison_iso_hom_comp_coordinateProjMap]
  apply pullback.hom_ext
  · rw [Category.assoc,hb,fromOfGlobalSections_comp_projToSpecCoeff,
      toSpecΓ_SpecMap_baseRingHom,Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_fst]
    exact hs
  · rw [Category.assoc,hi,fromOfGlobalSections_comp_coordinateProjMap,
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver_snd]

variable {V : Type u} [AddCommGroup V] [Module K V]
    (b : Module.Basis (Fin (n+1)) K V)

def moduleEvaluation {R : Type u} [CommRing R] (κ : K →+* R) (s : Fin (n+1) → R) :
    SymmetricAlgebra K V →+* R :=
  (MvPolynomial.eval₂Hom κ s).comp (SymPow.gradedMvPolynomialHom b).toRingHom

theorem map_irrelevant_moduleEvaluation (κ : K →+* Γ(T,⊤)) (s : Fin (n+1) → Γ(T,⊤))
    (hs : Ideal.span (Set.range s)=⊤) :
    (HomogeneousIdeal.irrelevant (fun d => SymPow.symmetricPower d K V)).toIdeal.map
      (moduleEvaluation b κ s)=⊤ := by
  have hh : (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal ≤
      (HomogeneousIdeal.irrelevant (fun d => SymPow.symmetricPower d K V)).toIdeal.map
        (SymPow.gradedMvPolynomialHom b).toRingHom :=
    irrelevant_le_map_gradedMvPolynomialHom b
  apply top_unique
  calc
    ⊤ = (HomogeneousIdeal.irrelevant (polyGrading K n)).toIdeal.map
        (MvPolynomial.eval₂Hom κ s) := (map_irrelevant_eval₂Hom_eq_top κ s hs).symm
    _ ≤ ((HomogeneousIdeal.irrelevant (fun d => SymPow.symmetricPower d K V)).toIdeal.map
        (SymPow.gradedMvPolynomialHom b).toRingHom).map (MvPolynomial.eval₂Hom κ s) :=
      Ideal.map_mono hh
    _ = _ := by rw [Ideal.map_map]; rfl

/-- A chart defined by actual functions, transported to the actual
projective-module scheme, is precisely its symmetric-algebra evaluation map. -/
theorem fromSections_comp_basisIso (f : T ⟶ Spec (.of K))
    (s : Fin (n+1) → Γ(T,⊤)) (hs : Ideal.span (Set.range s)=⊤) :
    Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver s hs f ≫ (basisProjectiveSpaceIso b).hom=
      Proj.fromOfGlobalSections (fun d => SymPow.symmetricPower d K V)
        (moduleEvaluation b (baseRingHom f) s)
        (map_irrelevant_moduleEvaluation b (baseRingHom f) s hs) := by
  rw [← fromEvaluation_comp_comparison_inv f s hs,basisProjectiveSpaceIso_hom]
  simp only [Category.assoc,Iso.inv_hom_id_assoc]
  exact Proj.fromOfGlobalSections_comp_map (SymPow.gradedMvPolynomialHom b)
    (irrelevant_le_map_gradedMvPolynomialHom b) (MvPolynomial.eval₂Hom (baseRingHom f) s)
    (map_irrelevant_eval₂Hom_eq_top (baseRingHom f) s hs)
    (map_irrelevant_moduleEvaluation b (baseRingHom f) s hs)


end M9Native.LagrangianProjectiveSections

namespace M9Native.LagrangianProjectiveSections
variable {K U V : Type u} [CommRing K] [AddCommGroup U] [Module K U]
  [AddCommGroup V] [Module K V] {m n : ℕ} {T : Scheme.{u}}

theorem fromSections_comp_linearMap
    (bU : Module.Basis (Fin (m+1)) K U) (bV : Module.Basis (Fin (n+1)) K V)
    (F : U →ₗ[K] V) (hF : Function.Surjective F) (p : T ⟶ Spec (.of K))
    (sU : Fin (m+1) → Γ(T,⊤)) (hU : Ideal.span (Set.range sU)=⊤)
    (sV : Fin (n+1) → Γ(T,⊤)) (hV : Ideal.span (Set.range sV)=⊤)
    (hEq : (moduleEvaluation bV (baseRingHom p) sV).comp
      (SymPow.gradedSymAlgMap F).toRingHom=moduleEvaluation bU (baseRingHom p) sU) :
    (Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sV hV p ≫
        (basisProjectiveSpaceIso bV).hom) ≫
      Proj.map (SymPow.gradedSymAlgMap F)
        (Proj.irrelevant_le_map_of_surjective _ (SymPow.symAlgMap_surjective F hF))=
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceOver sU hU p ≫
        (basisProjectiveSpaceIso bU).hom := by
  rw [fromSections_comp_basisIso,fromSections_comp_basisIso]
  have hComp : (HomogeneousIdeal.irrelevant (fun d => SymPow.symmetricPower d K U)).toIdeal.map
      ((moduleEvaluation bV (baseRingHom p) sV).comp (SymPow.gradedSymAlgMap F).toRingHom)=⊤ := by
    rw [hEq]
    exact map_irrelevant_moduleEvaluation bU (baseRingHom p) sU hU
  rw [Proj.fromOfGlobalSections_comp_map (SymPow.gradedSymAlgMap F)
    (Proj.irrelevant_le_map_of_surjective _ (SymPow.symAlgMap_surjective F hF))
    (moduleEvaluation bV (baseRingHom p) sV)
    (map_irrelevant_moduleEvaluation bV (baseRingHom p) sV hV) hComp]
  congr 1


end M9Native.LagrangianProjectiveSections
