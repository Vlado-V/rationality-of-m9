module

public import M9StacksIntegration.MukaiProjectiveEvaluationPoint

/-! # Literal transport from native homogeneous coordinates to a module projective point -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpaceOfModule
open Stacks.AlgebraicGeometry.ProjBaseChange Stacks.AlgebraicGeometry.ProjPolyChart
open M9Native.MukaiProjectiveEvaluationPoint

universe u

namespace M9Native.MukaiProjectiveCoordinateTransport

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse

variable (K V : Type u) [Field K] [AddCommGroup V] [Module K V]
variable {n : ℕ} (b : Module.Basis (Fin (n+1)) K V)

private theorem projSections_congr {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (G : ℕ → σ) [GradedRing G] (f g : A →+* Γ(Spec (.of K), ⊤))
    (hf : (HomogeneousIdeal.irrelevant G).toIdeal.map f = ⊤)
    (hg : (HomogeneousIdeal.irrelevant G).toIdeal.map g = ⊤) (hfg : f = g) :
    Proj.fromOfGlobalSections G f hf = Proj.fromOfGlobalSections G g hg := by
  subst g
  rfl

theorem span_scalarSections (w : Fin (n+1) → K) (i : Fin (n+1)) (hi : w i = 1) :
    Ideal.span (Set.range (fun j => scalarSections K (w j))) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← (scalarSections K).map_one,← hi]
  exact Ideal.subset_span ⟨i,rfl⟩

theorem polynomialSections_comp_integral (w : Fin (n+1) → K) :
    (polynomialSections K w).comp (integralGradedHom K n).toRingHom =
      Stacks.SectionsToProjectiveSpace.sectionsHom (fun j => scalarSections K (w j)) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp only [RingHom.comp_apply,polynomialSections,
      Stacks.SectionsToProjectiveSpace.sectionsHom,MvPolynomial.eval₂Hom_C]
    erw [integralGradedHom_apply,MvPolynomial.map_C,MvPolynomial.eval_C]
    rcases c with ⟨c⟩
    change scalarSections K (c : K) = (c : Γ(Spec (.of K), ⊤))
    exact map_intCast (scalarSections K) c
  · intro i
    simp [polynomialSections,integralGradedHom_apply]

def basisNativeMorphism (φ : Module.Dual K V) (i : Fin (n+1)) (hi : φ (b i) = 1) :
    Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K) :=
  evaluationMorphism K V φ (b i) hi ≫ (basisProjectiveSpaceIso b).inv

theorem basisNativeMorphism_toSpec (φ : Module.Dual K V) (i : Fin (n+1)) (hi : φ (b i) = 1) :
    basisNativeMorphism K V b φ i hi ≫
      pullback.fst (terminal.from (Spec (.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = 𝟙 _ := by
  have he : (basisProjectiveSpaceIso b).inv ≫
      pullback.fst (terminal.from (Spec (.of K)))
        (terminal.from (projectiveSpaceAtUniverse.{u} n)) = projectiveSpaceOfModuleToSpec K V := by
    rw [← basisProjectiveSpaceIso_hom_comp_toSpec b,← Category.assoc,Iso.inv_hom_id,Category.id_comp]
  rw [basisNativeMorphism,Category.assoc,he,evaluationMorphism_toSpec]

theorem basisNativeMorphism_toIntegral (φ : Module.Dual K V) (i : Fin (n+1)) (hi : φ (b i) = 1) :
    basisNativeMorphism K V b φ i hi ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (fun j => scalarSections K (φ (b j))) (span_scalarSections K _ i hi) := by
  have hcomp : (HomogeneousIdeal.irrelevant (polyGrading (ULift.{u} ℤ) n)).toIdeal.map
      ((polynomialSections K (fun j => φ (b j))).comp (integralGradedHom K n).toRingHom) = ⊤ := by
    rw [polynomialSections_comp_integral]
    exact Stacks.SectionsToProjectiveSpace.map_irrelevant_eq_top _ (span_scalarSections K _ i hi)
  have hnat := MukaiProjSectionsNaturality.fromOfGlobalSections_comp_map
    (polyGrading (ULift.{u} ℤ) n) (polyGrading K n) (integralGradedHom K n)
    (polynomialSections K (fun j => φ (b j))) (irrelevant_le_map_integralGradedHom K n)
    (map_irrelevant_polynomialSections K _ i hi) hcomp
  have hnat' := hnat.trans (projSections_congr K (polyGrading (ULift.{u} ℤ) n) _ _ hcomp
    (Stacks.SectionsToProjectiveSpace.map_irrelevant_eq_top _ (span_scalarSections K _ i hi))
    (polynomialSections_comp_integral K (fun j => φ (b j))))
  calc
    basisNativeMorphism K V b φ i hi ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
        (evaluationMorphism K V φ (b i) hi ≫
          ((basisProjectiveSpaceIso b).inv ≫ (polynomialComparison K n).iso.hom)) ≫
            coordinateProjMap K n (integralGradedHom K n) (mapDomain_integralGradedHom_eq_top K n) := by
      simp only [basisNativeMorphism,Category.assoc]
      erw [(polynomialComparison K n).toIntegral]
    _ = polynomialMorphism K (fun j => φ (b j)) i hi ≫
        Proj.map (integralGradedHom K n) (irrelevant_le_map_integralGradedHom K n) := by
      rw [basis_inverse_polynomial,evaluationMorphism_polynomial,coordinateProjMap_eq_projMap]
    _ = _ := hnat'

/-- The native coordinate morphism and basis isomorphism really produce the evaluation morphism.
The assumptions are the two actual projections of the coordinate morphism, not a point identity. -/
theorem coordinateTransport_eq (q : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K))
    (φ : Module.Dual K V) (i : Fin (n+1)) (hi : φ (b i) = 1)
    (hq : q ≫ pullback.fst (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = 𝟙 _)
    (hint : q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (fun j => scalarSections K (φ (b j))) (span_scalarSections K _ i hi)) :
    q ≫ (basisProjectiveSpaceIso b).hom = evaluationMorphism K V φ (b i) hi := by
  have he : q = basisNativeMorphism K V b φ i hi := by
    apply pullback.hom_ext
    · rw [hq,basisNativeMorphism_toSpec]
    · exact hint.trans (basisNativeMorphism_toIntegral K V b φ i hi).symm
  rw [he,basisNativeMorphism,Category.assoc,Iso.inv_hom_id,Category.comp_id]

/-- Actual native coordinate point transport, without an assumed kernel or Plücker point. -/
theorem coordinateTransport_base (q : Spec (.of K) ⟶ projectiveSpaceOverRing n (.of K))
    (φ : Module.Dual K V) (hφ : φ ≠ 0) (i : Fin (n+1)) (hi : φ (b i) = 1)
    (hq : q ≫ pullback.fst (terminal.from (Spec (.of K)))
      (terminal.from (projectiveSpaceAtUniverse.{u} n)) = 𝟙 _)
    (hint : q ≫ projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of K)) =
      Stacks.SectionsToProjectiveSpace.toProjectiveSpaceAtUniverse
        (fun j => scalarSections K (φ (b j))) (span_scalarSections K _ i hi))
    (x : Spec (.of K)) :
    (q ≫ (basisProjectiveSpaceIso b).hom) x = linearFunctionalPoint K V φ hφ := by
  rw [coordinateTransport_eq K V b q φ i hi hq hint,evaluationMorphism_base]

end M9Native.MukaiProjectiveCoordinateTransport
