module

public import M9StacksIntegration.CanonicalDivisorEvaluation
public import M9StacksIntegration.ProjectiveAffineFrameSpan
public import M9StacksIntegration.LineFramePullback
public import StacksFrontier.AlgebraicGeometry.ProductFamilyTwist.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceModuli.OverBase

/-! An actual finite divisor and its ORIGINAL projective coordinates.
A genuine finite-dimensional quotient of its actual section evaluation
constructs a smaller native projective map and an equality of scheme
morphisms. There is no projective-span or map-equality premise. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AmpleProjectiveImmersion Stacks.ProjectiveSpaceModuli
open Stacks.ProjectiveFromSections Stacks.ProjectiveSpaceChartRatio
open scoped BigOperators

universe u

namespace M9Native.DivisorProjectiveSpan

variable {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) {n : ℕ}
    (κ : X ⟶ projectiveSpaceOver n (Spec (.of K)))
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L]
    (e : (Scheme.Modules.pullback κ).obj
      (projectiveSpaceTwistingSheaf n (Spec (.of K))) ≅ L)

def originalSection (j : Fin (n+1)) : Γ(L, ⊤) :=
  e.hom.app ⊤ (pullbackGlobalSections κ
    (projectiveSpaceTwistingSheaf n (Spec (.of K)))
    (projectiveSpaceCoordSection n (Spec (.of K)) j))

/-- The actual coordinate H0 classes in the original projective basis. -/
def coordinateH0 : (Fin (n+1) → K) →ₗ[K] cohomologyOverField K f L 0 :=
  Fintype.linearCombination K (fun j =>
    (cohomologyOverFieldZeroLinearIso K f L).inv (originalSection κ e j))

theorem coordinateH0_basis (j : Fin (n+1)) :
    coordinateH0 f κ e (Pi.single j 1) =
      (cohomologyOverFieldZeroLinearIso K f L).inv (originalSection κ e j) := by
  classical
  simp [coordinateH0, Fintype.linearCombination_apply, Pi.single_apply]

def divisorSection (D : X.IdealSheafData) (j : Fin (n+1)) :
    Γ((Scheme.Modules.pullback D.subschemeι).obj L, ⊤) :=
  pullbackGlobalSections D.subschemeι L (originalSection κ e j)

theorem evaluation_coordinate (D : X.IdealSheafData) (j : Fin (n+1)) :
    CanonicalDivisorEvaluation.evaluation f D L
      (coordinateH0 f κ e (Pi.single j 1)) = divisorSection κ e D j := by
  rw [coordinateH0_basis, CanonicalDivisorEvaluation.evaluation_apply,
    Iso.inv_hom_id_apply]
  rfl

/-- The genuine composed pullback of the original O(1) comparison. -/
def divisorCoordinateIso (D : X.IdealSheafData) :
    (Scheme.Modules.pullback (D.subschemeι ≫ κ)).obj
      (projectiveSpaceTwistingSheaf n (Spec (.of K))) ≅
        (Scheme.Modules.pullback D.subschemeι).obj L :=
  ((Scheme.Modules.pullbackComp D.subschemeι κ).app
    (projectiveSpaceTwistingSheaf n (Spec (.of K)))).symm ≪≫
      (Scheme.Modules.pullback D.subschemeι).mapIso e

theorem divisorCoordinateIso_coordinate (D : X.IdealSheafData) (j : Fin (n+1)) :
    (divisorCoordinateIso κ e D).hom.app ⊤
      (pullbackGlobalSections (D.subschemeι ≫ κ)
        (projectiveSpaceTwistingSheaf n (Spec (.of K)))
        (projectiveSpaceCoordSection n (Spec (.of K)) j)) =
      divisorSection κ e D j := by
  change (((Scheme.Modules.pullback D.subschemeι).map e.hom).app ⊤
    (((Scheme.Modules.pullbackComp D.subschemeι κ).inv.app
      (projectiveSpaceTwistingSheaf n (Spec (.of K)))).app ⊤
      (pullbackGlobalSections (D.subschemeι ≫ κ)
        (projectiveSpaceTwistingSheaf n (Spec (.of K)))
        (projectiveSpaceCoordSection n (Spec (.of K)) j)))) = _
  rw [LineFramePullback.pullbackComp_inv_apply,
    SectionZeroIdealFactorization.pullback_map_app_pullbackGlobalSections]
  rfl

theorem divisorSection_generates (D : X.IdealSheafData) :
    GeneratesStalks (divisorSection κ e D) := by
  have h := Stacks.ProductFamilyTwist.generatesStalks_congr
    (divisorCoordinateIso κ e D)
    (pullbackTuple (D.subschemeι ≫ κ)
      (universalTupleOver n (Spec (.of K)))).generates
  have he : (fun j => (divisorCoordinateIso κ e D).hom.app ⊤
      (pullbackGlobalSections (D.subschemeι ≫ κ)
        (projectiveSpaceTwistingSheaf n (Spec (.of K)))
        (projectiveSpaceCoordSection n (Spec (.of K)) j))) =
      divisorSection κ e D := by
    funext j
    exact divisorCoordinateIso_coordinate κ e D j
  exact he ▸ h

/-- The actual original restricted map is the map of these genuine
sections, by native projective representability. -/
theorem restrictedMap_eq_toProjectiveSpace (D : X.IdealSheafData)
    (hκ : κ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of K)) = f) :
    D.subschemeι ≫ κ = toProjectiveSpaceOver (divisorSection κ e D)
      (divisorSection_generates κ e D) (D.subschemeι ≫ f) := by
  apply (eq_toProjectiveSpaceOver_iff (divisorSection κ e D)
    (divisorSection_generates κ e D) (D.subschemeι ≫ f) (D.subschemeι ≫ κ)).mpr
  refine ⟨?_, divisorCoordinateIso κ e D, divisorCoordinateIso_coordinate κ e D⟩
  exact congrArg (fun t => D.subschemeι ≫ t) hκ

/-- A real linear quotient of the actual coordinate evaluation gives
an actual smaller projective factor, in ANY quotient dimension. -/
theorem factor_of_evaluation_quotient (D : X.IdealSheafData)
    [IsFinite (D.subschemeι ≫ f)]
    (hκ : κ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of K)) = f)
    {m : ℕ} (q : (Fin (n+1) → K) →ₗ[K] (Fin (m+1) → K))
    (hq : Function.Surjective q)
    (g : (Fin (m+1) → K) →ₗ[K] CanonicalDivisorEvaluation.sectionsOnDivisor f D L)
    (hfactor : g.comp q = (CanonicalDivisorEvaluation.evaluation f D L).comp
      (coordinateH0 f κ e)) :
    ∃ t : D.subscheme ⟶ projectiveSpaceOver m (Spec (.of K)),
      t ≫ Stacks.Tag01VT.projectiveSpaceHom m (Spec (.of K)) = D.subschemeι ≫ f ∧
      t ≫ ProjectiveLinearSystemFactor.embedding K
        (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin (m+1))) q hq = D.subschemeι ≫ κ := by
  let LD := (Scheme.Modules.pullback D.subschemeι).obj L
  letI : Stacks.Ample.IsInvertibleModule D.subscheme LD :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback D.subschemeι L
  let sU := divisorSection κ e D
  let sV : Fin (m+1) → Γ(LD, ⊤) := fun i => g (Pi.single i 1)
  have hrel (j : Fin (n+1)) : sU j =
      ∑ i : Fin (m+1), baseRingHom (D.subschemeι ≫ f)
        ((Pi.basisFun K (Fin (m+1))).repr (q ((Pi.basisFun K (Fin (n+1))) j)) i) • sV i := by
    have h := CanonicalDivisorEvaluation.sections_expansion_structural f
      (Pi.basisFun K (Fin (n+1))) D L (coordinateH0 f κ e) q g hfactor j
    simpa only [sU, sV, divisorSection, Pi.basisFun_apply, coordinateH0_basis, Iso.inv_hom_id_apply,
      Pi.basisFun_repr, baseRingHom] using h
  have hU := divisorSection_generates κ e D
  have hV := ProjectiveLinearSystemFactor.generatesStalks_of_expansion K
    (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin (m+1))) q
    (D.subschemeι ≫ f) sU hU sV hrel
  letI : IsAffine D.subscheme := isAffine_of_isAffineHom (D.subschemeι ≫ f)
  letI : DiscreteTopology D.subscheme :=
    Stacks.AlgebraicGeometry.ComponentDegrees.discreteTopology_of_isProper_of_topologicalKrullDim_le_zero
      K (D.subschemeι ≫ f)
      (ProjectiveQuadraticDimension.dimension_le_zero_of_finite K (D.subschemeι ≫ f))
  obtain ⟨eD⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology D.subscheme LD
  let frame : LD ≅ ProjectiveSectionFunctions.UnitLine D.subscheme := eD
  have hspanU := ProjectiveLinearSystemFactor.affine_span_range_of_unit_generates
    (fun j => (show Γ(D.subscheme, ⊤) from frame.hom.app ⊤ (sU j)))
    (Stacks.ProductFamilyTwist.generatesStalks_congr frame hU)
  have hspanV := ProjectiveLinearSystemFactor.affine_span_range_of_unit_generates
    (fun i => (show Γ(D.subscheme, ⊤) from frame.hom.app ⊤ (sV i)))
    (Stacks.ProductFamilyTwist.generatesStalks_congr frame hV)
  refine ⟨toProjectiveSpaceOver sV hV (D.subschemeι ≫ f),
    toProjectiveSpaceOver_fst sV hV (D.subschemeι ≫ f), ?_⟩
  exact (ProjectiveLinearSystemFactor.framed_triangle K
    (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin (m+1))) q hq
    (D.subschemeι ≫ f) sU hU sV hV frame hspanU hspanV hrel).trans
      (restrictedMap_eq_toProjectiveSpace f κ e D hκ).symm

/-- The same actual factor through the native polynomial Proj models,
with the literal graded quotient used by the quadratic restriction API. -/
theorem polynomial_factor_of_evaluation_quotient (D : X.IdealSheafData)
    [IsFinite (D.subschemeι ≫ f)]
    (hκ : κ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of K)) = f)
    {m : ℕ} (q : (Fin (n+1) → K) →ₗ[K] (Fin (m+1) → K))
    (hq : Function.Surjective q)
    (g : (Fin (m+1) → K) →ₗ[K] CanonicalDivisorEvaluation.sectionsOnDivisor f D L)
    (hfactor : g.comp q = (CanonicalDivisorEvaluation.evaluation f D L).comp
      (coordinateH0 f κ e)) :
    ∃ t : D.subscheme ⟶ AlgebraicGeometry.Proj
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K m),
      t ≫ Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K m = D.subschemeι ≫ f ∧
      t ≫ ProjectiveLinearSystemFactor.polynomialEmbedding K
        (Pi.basisFun K (Fin (n+1))) (Pi.basisFun K (Fin (m+1))) q hq =
          (D.subschemeι ≫ κ) ≫
            (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).iso.hom := by
  obtain ⟨t, htbase, ht⟩ := factor_of_evaluation_quotient f κ e D hκ q hq g hfactor
  let cmp := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K m
  refine ⟨t ≫ cmp.iso.hom, ?_, ?_⟩
  · rw [Category.assoc,
      Stacks.ProjectiveSpaceChartRatio.polynomialComparison_iso_hom_comp_projToSpecCoeff]
    exact htbase
  · have h := congrArg (fun z => z ≫
      (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).iso.hom) ht
    simpa only [ProjectiveLinearSystemFactor.embedding, Category.assoc,
      Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id] using h

end M9Native.DivisorProjectiveSpan
