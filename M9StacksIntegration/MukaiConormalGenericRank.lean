module

public import M9StacksIntegration.MukaiKernelCubicIsomorphism
public import M9StacksIntegration.MukaiCanonicalCubicObstruction

@[expose] public section

/-! The actual conormal evaluation has generic rank seven. The bad
rank branch constructs the original kernel line and its actual cubic
isomorphism; the native canonical degree then gives 3 deg(L)=-16.
No rank-seven, line-valued-cubic, or isomorphism premise is supplied.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiConormalGenericRank

open MukaiCubicCurveKernel MukaiPrimitiveCanonicalEvaluation MukaiConormalKernelLine
open MukaiKernelCubicIsomorphism

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)

theorem mapRankAt_le_seven (x : X) :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x ≤ 7 := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (curveSource K f E b d) 7 :=
    curveSource_rank K f E b d
  let := TupleEvaluationFiber.residueAlgebra x
  let := TupleEvaluationFiber.fiberFinite (curveSource K f E b d) 7 x
  have hd := (TupleEvaluationFiber.inducedFiberMap (curveEvaluationMap K f E b d) x).finrank_range_add_finrank_ker
  rw [TupleEvaluationFiber.finrank_fiber (curveSource K f E b d) 7 x] at hd
  change MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x + _ = 7 at hd
  omega

variable [IsCurve K f] [Smooth f] [IsProper f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

theorem not_generic_rank_le_six
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) :
    ¬ MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) ≤ 6 := by
  intro hbad
  let L := curveKernel K f E b d
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} L 1 :=
    kernel_rank_one K f E b d hσ hsemi hbad
  let : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.InvertibleRankOneScheme.isInvertibleModule_iff_isFiniteLocallyFreeOfRank_one X L).mpr inferInstance
  obtain ⟨e,_he⟩ := exists_cubic_iso K f E b d hσ hsemi hbad
  exact MukaiCanonicalCubicObstruction.no_canonical_cubeLine_iso K f
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f))) E c hg L e

theorem generic_rank_seven
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) :
    MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X) = 7 := by
  have hlo := not_generic_rank_le_six K f E b d hσ hsemi c hg
  have hhi := mapRankAt_le_seven K f E b d (genericPoint X)
  omega

/-- The original actual curve has a closed point of full conormal
evaluation rank; no good-point or nonempty-open premise is assumed. -/
theorem exists_closed_full_rank
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (c : Scheme.Modules.exteriorPower E (3 : ℤ) ≅ Stacks.Duality.dualizingSheafOverField f)
    (hg : genus f = 9) :
    ∃ x : X, IsClosed ({x} : Set X) ∧
      MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x = 7 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular (isRegular_of_smooth_over_field f)
  let : JacobsonSpace X := ClosedPointCurveRank.jacobsonSpace_of_curve K f
  let := determinantH0_finite K f E
  let U := {x : X | 7 ≤ MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x}
  have hU : IsOpen U := MukaiGenericRankBound.isOpen_mapRankAt_ge
    (curveEvaluationMap K f E b d) 7 (finrank K (DeterminantH0 K f E))
    (curveSource_rank K f E b d)
    (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))) 7
  have hη : genericPoint X ∈ U := by
    change 7 ≤ MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) (genericPoint X)
    rw [generic_rank_seven K f E b d hσ hsemi c hg]
  obtain ⟨x,hxU,hxc⟩ := nonempty_inter_closedPoints (Z := U) ⟨genericPoint X,hη⟩ hU.isLocallyClosed
  refine ⟨x,hxc,?_⟩
  have hhi := mapRankAt_le_seven K f E b d x
  change 7 ≤ MukaiSemiIrreducible.mapRankAt (curveEvaluationMap K f E b d) x at hxU
  omega

end M9Native.MukaiConormalGenericRank
