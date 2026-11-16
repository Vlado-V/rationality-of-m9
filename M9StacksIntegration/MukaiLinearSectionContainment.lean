module

public import M9StacksIntegration.MukaiPrimitiveCanonicalDiagram
public import M9StacksIntegration.MukaiCanonicalBundleOnSmoothCurve
public import M9StacksIntegration.LagrangianMatrixPointRows
public import M9StacksIntegration.LagrangianFibreFactorization
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The original Mukai curve maps into an actual incidence fibre

The fixed fourteen coefficients are the coefficients of the original
primitive determinant sections. Rank-nullity produces five independent
actual canonical-evaluation relations, before lambda-three surjectivity.
The actual pullback formulas turn those relations into vanishing of the
original incidence equations. The native universal zero-scheme property
then constructs a map of the original curve into an original incidence
fibre, retaining its original LG and base maps.

This is containment. Closed immersion, transversality and equality with
the complete linear section are subsequent geometric proof obligations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open scoped BigOperators

universe u

namespace M9Native.MukaiLinearSectionContainment

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) (E : X.Modules) [IsProper f]

/-- Evaluation of literal coefficients in the original fourteen determinant sections. -/
def coordinateCanonicalEvaluation (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f) :
    (Fin 14 → k) →ₗ[k] cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0 :=
  ∑ i : Fin 14, (LinearMap.proj i).smulRight
    (canonicalEvaluation k f E b c ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis i))

theorem coordinateCanonicalEvaluation_apply (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (v : Fin 14 → k) :
    coordinateCanonicalEvaluation k f E b c v = ∑ i : Fin 14, v i •
      canonicalEvaluation k f E b c ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis i) := by
  simp only [coordinateCanonicalEvaluation, LinearMap.sum_apply, LinearMap.smulRight_apply,
    LinearMap.proj_apply]

/-- The genuine canonical H0 dimension gives five actual coefficient
relations, independently of lambda-three surjectivity. -/
theorem kernel_atLeast_five [IsCurve k f] (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) :
    5 ≤ finrank k (LinearMap.ker (coordinateCanonicalEvaluation k f E b c)) := by
  have h9 : finrank k (cohomologyOverField k f
      (Stacks.Duality.dualizingSheafOverField f) 0) = 9 :=
    (Stacks.Duality.finrank_cohomologyOverField_zero_dualizingSheafOverField f
      (IsCurve.topologicalKrullDim_eq_one f).le).trans hg
  letI : FiniteDimensional k
      (cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) :=
    Module.finite_of_finrank_pos (by rw [h9]; decide)
  have hd := (coordinateCanonicalEvaluation k f E b c).finrank_range_add_finrank_ker
  have hr := Submodule.finrank_le (LinearMap.range (coordinateCanonicalEvaluation k f E b c))
  have h14 : finrank k (Fin 14 → k) = 14 := by simp
  rw [h14] at hd
  rw [h9] at hr
  omega

omit [CharZero k] in
private theorem exists_relation_matrix {W : Type u} [AddCommGroup W] [Module k W]
    (D : (Fin 14 → k) →ₗ[k] W) (h : 5 ≤ finrank k (LinearMap.ker D)) :
    ∃ M : Matrix (Fin 5) (Fin 14) k, Function.Surjective M.mulVec ∧
      ∀ j : Fin 5, D (M j) = 0 := by
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank h
  let M : Matrix (Fin 5) (Fin 14) k := fun j => (v j).val
  have hrow : LinearIndependent k M.row :=
    hv.map' (LinearMap.ker D).subtype (by simp)
  exact ⟨M, hrow.mulVec_surjective, fun j => (v j).property⟩

/-- Every actual canonical evaluation relation is an actual vanishing
of the corresponding original determinant section along the original LG map. -/
theorem pullback_row_zero_of_relation (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) (M : Matrix (Fin 5) (Fin 14) k) (j : Fin 5)
    (hj : coordinateCanonicalEvaluation k f E b c (M j) = 0) :
    pullbackGlobalSections d.map (LagrangianPluckerQuotient.determinantLine k)
      (LagrangianSymmetricPlucker.sectionLinear k
        (LagrangianProjectiveLinearForms.rowForms k M.mulVecLin j)) = 0 := by
  apply (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((d.canonicalIso k f E c).hom.app ⊤)).injective).mp
  rw [LagrangianParameterRowComparison.pullback_rowSection, map_sum]
  have hκ : LagrangianParameterRowComparison.scalarMap k
      (d.map ≫ LagrangianGrassmannian.projection k) = ExteriorEvaluation.baseRingMap k f :=
    d.coefficients k f E
  simp only [Scheme.Modules.Hom.app_smul, hκ, d.canonicalCoordinates k f E c]
  have hscalar (a : k)
      (s : cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) :
      (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
          (a • s) = ExteriorEvaluation.baseRingMap k f a •
        (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f
      (Stacks.Duality.dualizingSheafOverField f)).hom.hom.map_smul a s
  have h := congrArg
    (fun z => (cohomologyOverFieldZeroLinearIso k f
      (Stacks.Duality.dualizingSheafOverField f)).hom z) hj
  rw [coordinateCanonicalEvaluation_apply, map_sum, map_zero] at h
  simpa only [hscalar] using h

/-- The five original incidence equations vanish as actual sheaf sections,
so the original zero-scheme universal property constructs the original fibre map. -/
theorem exists_fibre_lift_of_relations (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) (M : Matrix (Fin 5) (Fin 14) k)
    (hM : Function.Surjective M.mulVec)
    (hrows : ∀ j : Fin 5, coordinateCanonicalEvaluation k f E b c (M j) = 0) :
    ∃ q : X ⟶ LagrangianFibreFactorization.fibre k
        (LagrangianMatrixPointRows.matrixPoint k M hM),
      q ≫ LagrangianFibreFactorization.fibreToLG k
          (LagrangianMatrixPointRows.matrixPoint k M hM) = d.map ∧
      q ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint k M hM)
          (LagrangianLinearSections.familyProjection k) = f := by
  let p := LagrangianMatrixPointRows.matrixPoint k M hM
  have hp : p ≫ LagrangianLinearSections.parameterProjection k = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 k M hM
  let t := LagrangianFibreFactorization.fixedAmbient k p hp d.map
  have ht : t ≫ LagrangianLinearSections.toParameter k =
      ((t ≫ LagrangianLinearSections.toLG k) ≫ LagrangianGrassmannian.projection k) ≫ p := by
    rw [LagrangianFibreFactorization.fixedAmbient_toParameter,
      LagrangianFibreFactorization.fixedAmbient_toLG]
  have hf : ∃ z : X ⟶ LagrangianLinearSections.family k,
      z ≫ LagrangianLinearSections.inclusion k = t := by
    apply (LagrangianMatrixPointRows.factorsThrough_iff_original_rows k t M hM ht).mpr
    intro j
    rw [LagrangianFibreFactorization.fixedAmbient_toLG]
    exact pullback_row_zero_of_relation k f E b c d M j (hrows j)
  obtain ⟨q, hq⟩ :=
    (LagrangianFibreFactorization.fibre_factorsThrough_iff k p hp d.map).mpr hf
  refine ⟨q, hq, ?_⟩
  rw [LagrangianFibreFactorization.fibre_base k p hp, ← Category.assoc, hq, d.over_base]

/-- An actual canonical generated semi-irreducible bundle constructs an
actual original incidence-fibre containment, with no lambda-three,
closed-immersion, transversality or linear-section-isomorphism premise. -/
theorem exists_incidence_fibre_lift [IsAlgClosed k] [IsCurve k f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank k (H0 k f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3) :
    ∃ (n : NormalizedEvaluation k f E) (M : Matrix (Fin 5) (Fin 14) k)
      (hM : Function.Surjective M.mulVec)
      (q : X ⟶ LagrangianFibreFactorization.fibre k
        (LagrangianMatrixPointRows.matrixPoint k M hM)),
      q ≫ LagrangianFibreFactorization.fibreToLG k
          (LagrangianMatrixPointRows.matrixPoint k M hM) = n.diagram.map ∧
      q ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint k M hM)
          (LagrangianLinearSections.familyProjection k) = f := by
  let n := MukaiPrimitiveCanonicalDiagram.normalizedEvaluation_of_canonical k f E c hg hgen h6 hsemi
  obtain ⟨M, hM, hrows⟩ := exists_relation_matrix k
    (coordinateCanonicalEvaluation k f E n.basis c) (kernel_atLeast_five k f E n.basis c hg)
  obtain ⟨q, hq, hbase⟩ := exists_fibre_lift_of_relations k f E n.basis c n.diagram M hM hrows
  exact ⟨n, M, hM, q, hq, hbase⟩

/-- One original degree-eight net supplies the bundle and hence the actual
original incidence-fibre containment. Net existence remains a distinct
Brill--Noether theorem; no desired curve classification is assumed. -/
theorem exists_incidence_fibre_lift_from_net [IsAlgClosed k] [IsCurve k f] [Smooth f]
    (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (A : LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 8 2) :
    ∃ (E : X.Modules) (n : NormalizedEvaluation k f E) (M : Matrix (Fin 5) (Fin 14) k)
      (hM : Function.Surjective M.mulVec)
      (q : X ⟶ LagrangianFibreFactorization.fibre k
        (LagrangianMatrixPointRows.matrixPoint k M hM)),
      MukaiCanonicalBundleFromNet.IsCanonicalGeneratedSemi f E ∧
      q ≫ LagrangianFibreFactorization.fibreToLG k
          (LagrangianMatrixPointRows.matrixPoint k M hM) = n.diagram.map ∧
      q ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint k M hM)
          (LagrangianLinearSections.familyProjection k) = f := by
  obtain ⟨F, hF, _⟩ := MukaiCanonicalBundleOnSmoothCurve.exists_unique_up_to_iso_from_net f hg hnp A
  obtain ⟨hr, h6, ⟨c⟩, hgen, hsemi⟩ := hF
  letI := hr
  obtain ⟨n, M, hM, q, hq, hbase⟩ := exists_incidence_fibre_lift k f F c hg hgen h6 hsemi
  exact ⟨F, n, M, hM, q, ⟨hr, h6, ⟨c⟩, hgen, hsemi⟩, hq, hbase⟩

end M9Native.MukaiLinearSectionContainment
