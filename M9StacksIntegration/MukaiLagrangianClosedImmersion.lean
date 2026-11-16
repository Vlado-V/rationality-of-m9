module

public import M9StacksIntegration.MukaiLinearSectionContainment
public import M9StacksIntegration.MukaiCanonicalSeparation
public import M9StacksIntegration.MukaiEvaluationChoices
public import M9StacksIntegration.LagrangianFibreFiveSection
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoComplete

/-!
# The actual normalized LG map is an embedding after true lambda-three surjectivity

The canonical separation predicate is proved from the actual no-degree-five
pencil condition. The original pullback of the original determinant line
realizes the original complete canonical section space when the actual
lambda-three map is surjective. The native degree-two embedding criterion
then applies to the original normalized LG map itself.

Lambda-three surjectivity is a genuine explicit remaining input to this
leaf; it is owned by the actual curve-kernel/cubic argument. No embedding,
very-ampleness, section-pinning or curve-classification premise is used.
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

namespace M9Native.MukaiLagrangianClosedImmersion

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation MukaiLinearSectionContainment

variable {X : Scheme.{u}} (k : Type u) [Field k] [CharZero k]
  (f : X ⟶ Spec (.of k)) (E : X.Modules) [IsProper f]

omit [IsProper f] in
/-- True surjectivity of lambda-three gives true surjectivity of its
original primitive factor, with the actual complete basis retained. -/
theorem primitiveEvaluation_surjective (b : Basis (Fin 6) k (H0 k f E))
    (hb : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (hLambda : Function.Surjective (ExteriorEvaluation.lambda k f E 3)) :
    Function.Surjective (primitiveEvaluation k f E b) := by
  have hthree : Function.Surjective (lambdaThree k f E b) :=
    hLambda.comp (exteriorPower.map_surjective (n := 3) b.equivFun.symm.surjective)
  apply LinearMap.range_eq_top.mp
  rw [range_primitiveEvaluation k f E b hb]
  exact LinearMap.range_eq_top.mpr hthree

theorem canonicalEvaluation_surjective (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hb : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (hLambda : Function.Surjective (ExteriorEvaluation.lambda k f E 3)) :
    Function.Surjective (canonicalEvaluation k f E b c) :=
  (MukaiEvaluationChoices.cohomologyEquiv k f c 0).surjective.comp
    (primitiveEvaluation_surjective k f E b hb hLambda)

/-- The literal original fourteen coefficients exhaust canonical H0
when the actual lambda-three map is onto. -/
theorem coordinateCanonicalEvaluation_surjective (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hb : ExteriorEvaluation.lambda k f E 2 (basisSigma k f E b) = 0)
    (hLambda : Function.Surjective (ExteriorEvaluation.lambda k f E 3)) :
    Function.Surjective (coordinateCanonicalEvaluation k f E b c) := by
  intro y
  obtain ⟨ell, hell⟩ := canonicalEvaluation_surjective k f E b c hb hLambda y
  let B := (LagrangianPluckerLinear.primitiveBasis14 k).dualBasis
  refine ⟨fun i => B.repr ell i, ?_⟩
  calc
    _ = canonicalEvaluation k f E b c (∑ i : Fin 14, B.repr ell i • B i) := by
      simp only [coordinateCanonicalEvaluation_apply, map_sum, map_smul, B]
    _ = canonicalEvaluation k f E b c ell := congrArg _ (B.sum_repr ell)
    _ = y := hell

/-- Literal linear combinations of the original determinant sections,
using the actual original LG structural scalar map. -/
def determinantLinearSection (v : Fin 14 → k) :
    Γ(LagrangianPluckerQuotient.determinantLine k, ⊤) :=
  ∑ i : Fin 14, AlgebraicGeometry.baseRingMap (LagrangianGrassmannian.projection k) (v i) •
    LagrangianPluckerQuotient.primitiveSections k i

/-- The actual determinant-line pullback realizes every original
fourteen-coefficient canonical section, including the actual scalar action. -/
theorem determinantLinearSection_pullback (b : Basis (Fin 6) k (H0 k f E))
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (d : EvaluationDiagram k f E b) (v : Fin 14 → k) :
    (d.canonicalIso k f E c).hom.app ⊤
        (pullbackSectionTop d.map (LagrangianPluckerQuotient.determinantLine k)
          (determinantLinearSection k v)) =
      (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
        (coordinateCanonicalEvaluation k f E b c v) := by
  have hbase : AlgebraicGeometry.baseRingMap f = ExteriorEvaluation.baseRingMap k f := by
    have h := d.coefficients k f E
    change AlgebraicGeometry.baseRingMap
      (d.map ≫ LagrangianGrassmannian.projection k) = ExteriorEvaluation.baseRingMap k f at h
    rw [d.over_base] at h
    exact h
  have hcoord (i : Fin 14) :
      (d.canonicalIso k f E c).hom.app ⊤
          (pullbackSectionTop d.map (LagrangianPluckerQuotient.determinantLine k)
            (LagrangianPluckerQuotient.primitiveSections k i)) =
        (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
          (canonicalEvaluation k f E b c ((LagrangianPluckerLinear.primitiveBasis14 k).dualBasis i)) := by
    rw [← pullbackGlobalSections_eq_pullbackSectionTop]
    exact d.canonicalCoordinates k f E c i
  have hscalar (a : k)
      (s : cohomologyOverField k f (Stacks.Duality.dualizingSheafOverField f) 0) :
      (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
          (a • s) = ExteriorEvaluation.baseRingMap k f a •
        (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom s :=
    (cohomologyOverFieldZeroLinearIso k f
      (Stacks.Duality.dualizingSheafOverField f)).hom.hom.map_smul a s
  let P : Γ(LagrangianPluckerQuotient.determinantLine k, ⊤) →+
      Γ((Scheme.Modules.pullback d.map).obj (LagrangianPluckerQuotient.determinantLine k), ⊤) :=
    { toFun := pullbackSectionTop d.map (LagrangianPluckerQuotient.determinantLine k)
      map_zero' := pullbackSectionTop_zero d.map _
      map_add' := pullbackSectionTop_add d.map _ }
  have hsum (t : Fin 14 → Γ(LagrangianPluckerQuotient.determinantLine k, ⊤)) :
      pullbackSectionTop d.map (LagrangianPluckerQuotient.determinantLine k) (∑ i, t i) =
        ∑ i, pullbackSectionTop d.map (LagrangianPluckerQuotient.determinantLine k) (t i) :=
    map_sum P t Finset.univ
  rw [determinantLinearSection, hsum, map_sum]
  simp only [pullbackSectionTop_smul,
    Scheme.Modules.Hom.app_smul,
    AlgebraicGeometry.baseRingMap_comp f (LagrangianGrassmannian.projection k) d.map d.over_base,
    hbase, hcoord, coordinateCanonicalEvaluation_apply, map_sum, hscalar]

variable [IsAlgClosed k] [IsCurve k f] [Smooth f]

/-- The original normalized LG morphism is a closed immersion. The only
unfinished Mukai input is the true lambda-three surjectivity, explicitly
retained here for its separate geometric producer. -/
theorem normalized_map_isClosedImmersion
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (n : NormalizedEvaluation k f E)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hLambda : Function.Surjective (ExteriorEvaluation.lambda k f E 3)) :
    IsClosedImmersion n.diagram.map := by
  letI : IsProper (LagrangianGrassmannian.projection k) :=
    isProper_of_isProjectiveMorphism _ (LagrangianPluckerClosed.isProjectiveMorphism_projection k)
  letI : Stacks.Ample.IsInvertibleModule X (Stacks.Duality.dualizingSheafOverField f) :=
    CurveCanonicalInvertibility.dualizing_isInvertible f
  let ψ : (Fin 14 → k) → Γ(Stacks.Duality.dualizingSheafOverField f, ⊤) := fun v =>
    (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom
      (coordinateCanonicalEvaluation k f E n.basis c v)
  have hψ : Function.Surjective ψ :=
    (ConcreteCategory.bijective_of_isIso
      (cohomologyOverFieldZeroLinearIso k f (Stacks.Duality.dualizingSheafOverField f)).hom).surjective.comp
      (coordinateCanonicalEvaluation_surjective k f E n.basis c n.relation hLambda)
  exact isClosedImmersion_of_surjectsOnDegreeTwo n.diagram.map f
    (LagrangianGrassmannian.projection k) n.diagram.over_base (n.diagram.canonicalIso k f E c)
    (t := determinantLinearSection k) (ψ := ψ)
    (determinantLinearSection_pullback k f E n.basis c n.diagram) hψ
    (MukaiCanonicalSeparation.dualizing_surjectsOnDegreeTwo_of_no_degree_five f hnp)

omit [CharZero k] [IsAlgClosed k] in
/-- Every original rational parameter fibre has its actual closed LG immersion,
by the proved original five-section model comparison. -/
theorem fibreToLG_isClosedImmersion (p : Spec (.of k) ⟶ LagrangianLinearSections.parameter k)
    (hp : p ≫ LagrangianLinearSections.parameterProjection k = 𝟙 _) :
    IsClosedImmersion (LagrangianFibreFactorization.fibreToLG k p) := by
  obtain ⟨s, e, he⟩ := LagrangianFibreFiveSection.every_parameter_fiveSection k p hp
  have h : e.inv ≫ LagrangianFiveSectionModel.inclusion k s =
      LagrangianFibreFactorization.fibreToLG k p := by
    rw [← he, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  rw [← h]
  infer_instance

/-- The actual curve containment produced from the canonical bundle is
a closed immersion once its genuine lambda-three surjectivity is proved. -/
theorem exists_closed_fibre_lift
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) (hgen : MukaiSemiIrreducible.GloballyGenerated E)
    (h6 : finrank k (H0 k f E) = 6)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible k f E 3)
    (hnp : ¬ Nonempty (LinearSeries k f (IsCurve.topologicalKrullDim_eq_one f).le 5 1))
    (hLambda : Function.Surjective (ExteriorEvaluation.lambda k f E 3)) :
    ∃ (n : NormalizedEvaluation k f E) (M : Matrix (Fin 5) (Fin 14) k)
      (hM : Function.Surjective M.mulVec)
      (q : X ⟶ LagrangianFibreFactorization.fibre k
        (LagrangianMatrixPointRows.matrixPoint k M hM)),
      IsClosedImmersion q ∧
      q ≫ LagrangianFibreFactorization.fibreToLG k
          (LagrangianMatrixPointRows.matrixPoint k M hM) = n.diagram.map ∧
      q ≫ pullback.fst (LagrangianMatrixPointRows.matrixPoint k M hM)
          (LagrangianLinearSections.familyProjection k) = f := by
  obtain ⟨n, M, hM, q, hq, hbase⟩ :=
    exists_incidence_fibre_lift k f E c hg hgen h6 hsemi
  letI := normalized_map_isClosedImmersion k f E c n hnp hLambda
  let p := LagrangianMatrixPointRows.matrixPoint k M hM
  have hp : p ≫ LagrangianLinearSections.parameterProjection k = 𝟙 _ :=
    SplitMatrixGrassmannian.fieldPoint_projection 9 14 k M hM
  letI := fibreToLG_isClosedImmersion k p hp
  letI : IsClosedImmersion (q ≫ LagrangianFibreFactorization.fibreToLG k p) := hq ▸ inferInstance
  exact ⟨n, M, hM, q, IsClosedImmersion.of_comp_isClosedImmersion q
    (LagrangianFibreFactorization.fibreToLG k p), hq, hbase⟩

end M9Native.MukaiLagrangianClosedImmersion
