module

public import M9StacksIntegration.MukaiActualLagrangianClosedImmersion
public import M9StacksIntegration.MukaiConormalGoodPoint
public import M9StacksIntegration.MukaiCanonicalCoefficientRelations
public import M9StacksIntegration.MukaiConormalRowJetImplication
public import M9StacksIntegration.MukaiCurveConormalDeterminant
public import M9StacksIntegration.CurveMapPointDeterminantCriterion

@[expose] public section

/-!
# Invertibility of the actual original Mukai row-to-conormal map

The actual primitive-evaluation rank argument constructs a genuine point
where its kernel meets the full LG first-jet kernel trivially. Original
incidence equations put each original row combination in the first
kernel. The actual local row/differential normalization puts the kernel
of the actual conormal map in the second. Row independence proves actual
point injectivity. The genuine determinant-line comparison then upgrades
it to invertibility everywhere on the original curve.

No determinant comparison, point-injectivity, generic-rank or desired
conormal isomorphism is supplied as a premise. The native no-degree-five
hypothesis is used only through the separately proved actual canonical
closed embedding. Legacy visibility is retained for the frozen actual
rank producer; its source is not modified.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Matrix
open M9Native.MukaiBundleDeterminant
universe u

namespace M9Native.MukaiCurveConormalIsomorphism

open MukaiLagrangianMap MukaiPrimitiveCanonicalEvaluation
open MukaiConormalOriginCoordinates LagrangianGrassmannian

variable {X : Scheme.{u}} (K : Type u) [Field K] [CharZero K] [IsAlgClosed K]
  (f : X ⟶ Spec (.of K)) [IsCurve K f] [Smooth f] [IsProper f]
  (E : X.Modules) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
  (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
  (n : NormalizedEvaluation K f E)
  (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
  (hg : genus f = 9)
  (M : Matrix (Fin 5) (Fin 14) K) (hM : Function.Surjective M.mulVec)
  (q : X ⟶ LagrangianFibreFactorization.fibre K
    (LagrangianMatrixPointRows.matrixPoint K M hM))
  (hq : q ≫ LagrangianFibreFactorization.fibreToLG K
    (LagrangianMatrixPointRows.matrixPoint K M hM) = n.diagram.map)

include c hsemi hg

private theorem exists_injective_point [IsClosedImmersion n.diagram.map] :
    ∃ p : Spec (.of K) ⟶ X,
      Function.Injective (moduleSpecΓFunctor.map ((Scheme.Modules.pullback p).map
        (LagrangianFibreConormalMap.sequenceMap K M hM n.diagram.map q hq))).hom := by
  obtain ⟨p,g,z,hp,hz,hzb,hsep⟩ :=
    MukaiConormalGoodPoint.exists_translated_relation_separating_point K f E c n hsemi hg
  have hpLG : p ≫ (n.diagram.map ≫ projection K) = 𝟙 _ := by
    rw [n.diagram.over_base, hp]
  have hi : Function.Injective
      (MukaiConormalRowFirstJet.pointSequenceMap K M hM n.diagram.map q hq p g z hz) := by
    apply LinearMap.ker_eq_bot.mp
    apply eq_bot_iff.mpr
    intro a ha
    change a = 0
    have hmu := MukaiCanonicalCoefficientRelations.primitiveEvaluation_zero_of_fibre_lift
      K f E n.basis c n.diagram M hM q hq a
    have hj := MukaiConormalRowFirstJet.pointSequenceMap_zero_implies_firstJet_zero
      K M hM n.diagram.map q hq p hpLG g z hz a ha
    have he := hsep ((formsCoordinates K).symm (a ᵥ* M)) hmu hj
    have hv : a ᵥ* M = (0 : Fin 5 → K) ᵥ* M := by
      simpa only [LinearEquiv.apply_symm_apply, map_zero, Matrix.zero_vecMul] using
        congrArg (formsCoordinates K) he
    exact MukaiCanonicalCoefficientRelations.rowCombination_injective K M hM hv
  refine ⟨p, ?_⟩
  let e := MukaiConormalRowFirstJet.pointSourceEquiv K n.diagram.map p g z hz
  intro x y hxy
  apply e.injective
  apply hi
  simpa only [e, MukaiConormalRowFirstJet.pointSequenceMap, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] using hxy

/-- The original geometric row map is invertible on the original curve.
Every rank, determinant and point assertion is derived from actual
curve/bundle/incidence data. -/
theorem normalized_sequenceMap_isIso
    (hnp : ¬ Nonempty (LinearSeries K f (IsCurve.topologicalKrullDim_eq_one f).le 5 1)) :
    letI := MukaiActualLagrangianClosedImmersion.normalized_map_isClosedImmersion
      K f E c n hsemi hg hnp
    IsIso (LagrangianFibreConormalMap.sequenceMap K M hM n.diagram.map q hq) := by
  letI := MukaiActualLagrangianClosedImmersion.normalized_map_isClosedImmersion
    K f E c n hsemi hg hnp
  obtain ⟨p,hp⟩ := exists_injective_point K f E c n hsemi hg M hM q hq
  letI := MukaiCurveConormalDeterminant.map_smoothOfRelativeDimension_one K f E n.basis n.diagram
  letI := LagrangianFibreConormalMap.source_rank K n.diagram.map
  letI := LagrangianFibreConormalMap.target_rank K n.diagram.map
  letI := MukaiCurveConormalDeterminant.curveLine_isInvertible K f E n.basis n.diagram
  letI := LagrangianCurveAdjunction.integerPower_isInvertible
    (MukaiCurveConormalDeterminant.curveLine K f E n.basis n.diagram) (-5)
  let eS := MukaiCurveConormalDeterminant.equationDualDeterminantIso K f E n.basis n.diagram
  let eT := MukaiCurveConormalDeterminant.conormalDeterminantIso K f E n.basis n.diagram c
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (topExterior (LagrangianFibreConormalMap.source K n.diagram.map) 5) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ eS.symm
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (topExterior (LagrangianCurveConormal.sequence K n.diagram.map).X₁ 5) :=
    Stacks.SheafOfModules.isInvertible_of_iso _ _ eT.symm
  exact CurveMapPointDeterminantCriterion.isIso_of_point_sections_injective_of_determinantIso
    K f 5 (LagrangianFibreConormalMap.sequenceMap K M hM n.diagram.map q hq)
    (MukaiCurveConormalDeterminant.determinantLineComparison K f E n.basis n.diagram c) p hp

end M9Native.MukaiCurveConormalIsomorphism
