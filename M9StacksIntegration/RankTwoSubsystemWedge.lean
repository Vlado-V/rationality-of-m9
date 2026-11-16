module

public import M9StacksIntegration.RankTwoSubsystemBundles
public import M9StacksIntegration.MukaiEvaluationMatrix
public import M9StacksIntegration.MukaiTripleDeterminantRank

/-!
# A genuinely nonzero pair wedge of the three original image sections

The image sections are the canonical lifts of the actual free generators
through the actual image factorization. Their evaluation is the actual
epimorphism onto that image. At any actual point of a rank-two image, their
residue values span a two-dimensional space, so TWO ORIGINAL generators
are independent. Their actual global exterior section is nonzero because
its residue wedge is nonzero. The genuine determinant comparison then
gives a nonzero global beta-section. No pair or section nonvanishing is
assumed, and no divisor degree is claimed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite

namespace M9Native.RankTwoSubsystemWedge
open RankTwoSubsystemBundles TupleEvaluationFiber
universe u v

section Linear
variable (L : Type u) [Field L] {V : Type v} [AddCommGroup V] [Module L V]

/-- Rank two in the span of three actual vectors selects two of those
very vectors, not linear combinations replacing them. -/
theorem exists_independent_pair (z : Fin 3 → V)
    (hz : finrank L (Submodule.span L (Set.range z)) = 2) :
    ∃ e : Fin 2 ↪ Fin 3, LinearIndependent L (z ∘ e) := by
  classical
  obtain ⟨ι, a, ha, hspan, hli⟩ := exists_linearIndependent' L z
  let : Finite ι := Finite.of_injective a ha
  let : Fintype ι := Fintype.ofFinite ι
  have hc : Fintype.card ι = 2 := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hli
    change Fintype.card ι = finrank L (Submodule.span L (Set.range (z ∘ a))) at h
    rwa [hspan, hz] at h
  let e : Fin 2 ≃ ι := (Fintype.equivFinOfCardEq hc).symm
  refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
  exact hli.comp e e.injective

end Linear

variable {X : Scheme.{u}} (K : Type u) [Field K] (f : X ⟶ Spec (.of K))
variable {G : X.Modules} (φ : freeThree X ⟶ G)

/-- The exact original free-generator sections, lifted through the
actual categorical image, at the original structural K-action on H0. -/
def imageSections (i : Fin 3) : cohomologyOverField K f (imageBundle φ) 0 :=
  MukaiEvaluationImage.liftedSectionH0 K f φ
    (_root_.SheafOfModules.freeSection (ULift.up i))

/-- These three actual H0 sections evaluate to the actual image
epimorphism, with no global-generation premise supplied. -/
theorem imageSections_evaluation :
    MukaiSemiIrreducible.evaluation K f (imageBundle φ) (imageSections K f φ) =
      factorThruImage φ := by
  apply MukaiEvaluationMatrix.freeHom_ext_top
  intro i
  rw [MukaiEvaluationMatrix.evaluation_basisSection]
  change (cohomologyOverFieldZeroLinearIso K f (image φ)).hom
    ((cohomologyOverFieldZeroLinearIso K f (image φ)).inv _) = _
  rw [Iso.inv_hom_id_apply]
  rfl

/-- The lift retains each original actual H0 section under the literal
image inclusion. -/
theorem imageSections_maps_to_original (s : Fin 3 → cohomologyOverField K f G 0)
    (i : Fin 3) :
    cohomologyOverFieldMap K f
      (image.ι (MukaiSemiIrreducible.evaluation K f G s)) 0
      (imageSections K f (MukaiSemiIrreducible.evaluation K f G s) i) = s i :=
  MukaiEvaluationImage.evaluation_lift_maps_to_section K f G s i

/-- The actual global exterior section of the selected two original
image sections. -/
def pairExteriorSection (e : Fin 2 ↪ Fin 3) :
    cohomologyOverField K f (Scheme.Modules.exteriorPower (imageBundle φ) (2 : ℤ)) 0 :=
  ExteriorEvaluation.lambda K f (imageBundle φ) 2
    (exteriorPower.ιMulti K 2 (imageSections K f φ ∘ e))

section Reduced
variable [IsReduced X] [IsLocallyNoetherian X]
  [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} G 3]

/-- Actual fibre rank at an actual point supplies a genuinely nonzero
global pair wedge among the three original generators. -/
theorem exists_pairExteriorSection_ne_zero
    (hr : MukaiSemiIrreducible.EverywhereRank φ 2) (x : X) :
    ∃ e : Fin 2 ↪ Fin 3, pairExteriorSection K f φ e ≠ 0 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (imageBundle φ) 2 :=
    imageBundle_rank φ hr
  let := residueAlgebra x
  let : Module.Finite (X.residueField x) (Fiber (imageBundle φ) x) :=
    fiberFinite (imageBundle φ) 2 x
  let : Epi (MukaiSemiIrreducible.evaluation K f (imageBundle φ) (imageSections K f φ)) := by
    rw [imageSections_evaluation]
    infer_instance
  have hsurj : Function.Surjective
      (tupleMap K f (imageBundle φ) (imageSections K f φ) x) := by
    rw [← evaluationFiber_comp_coordinates]
    exact (MukaiShortExactFiberRank.fiberMap_surjective _ x).comp
      (freeFiberCoordinates 3 x).surjective
  have hspan : finrank (X.residueField x)
      (Submodule.span (X.residueField x)
        (Set.range (fun i => sectionValue K f (imageBundle φ) x (imageSections K f φ i)))) = 2 := by
    have h : LinearMap.range (tupleMap K f (imageBundle φ) (imageSections K f φ) x) =
        Submodule.span (X.residueField x)
          (Set.range (fun i => sectionValue K f (imageBundle φ) x (imageSections K f φ i))) :=
      (Pi.basisFun (X.residueField x) (Fin 3)).constr_range (X.residueField x)
    rw [← h, LinearMap.range_eq_top.mpr hsurj, finrank_top, finrank_fiber (imageBundle φ) 2 x]
  obtain ⟨e, he⟩ := exists_independent_pair (X.residueField x) _ hspan
  refine ⟨e, ?_⟩
  intro hz
  apply MukaiTripleDeterminantRank.wedge_ne_zero_of_linearIndependent _ he
  exact ExteriorEvaluation.wedge_fiber_eq_zero_of_lambda_eq_zero
    K f x (X.residueField x) (imageBundle φ) 2 (imageSections K f φ ∘ e) hz

/-- The actual global beta-section is the actual pair wedge transported
through the proved native top-exterior/determinant isomorphism. -/
def pairBetaSection (hr : MukaiSemiIrreducible.EverywhereRank φ 2) (e : Fin 2 ↪ Fin 3) :
    cohomologyOverField K f (beta φ) 0 :=
  MukaiEvaluationChoices.cohomologyEquiv K f (betaExteriorIso φ hr).symm 0
    (pairExteriorSection K f φ e)

theorem pairBetaSection_formula (hr : MukaiSemiIrreducible.EverywhereRank φ 2)
    (e : Fin 2 ↪ Fin 3) :
    pairBetaSection K f φ hr e = cohomologyOverFieldMap K f (betaExteriorIso φ hr).inv 0
      (ExteriorEvaluation.lambda K f (imageBundle φ) 2
        (exteriorPower.ιMulti K 2 (imageSections K f φ ∘ e))) := rfl

/-- A real point and actual rank two prove existence of a nonzero
global determinant section coming from a pair of the three original sections. -/
theorem exists_pairBetaSection_ne_zero
    (hr : MukaiSemiIrreducible.EverywhereRank φ 2) (x : X) :
    ∃ e : Fin 2 ↪ Fin 3, pairBetaSection K f φ hr e ≠ 0 := by
  obtain ⟨e, he⟩ := exists_pairExteriorSection_ne_zero K f φ hr x
  refine ⟨e, ?_⟩
  intro hz
  apply he
  exact (MukaiEvaluationChoices.cohomologyEquiv K f (betaExteriorIso φ hr).symm 0).injective
    (hz.trans (map_zero _).symm)

end Reduced
end M9Native.RankTwoSubsystemWedge
