module

public import M9StacksIntegration.MukaiCubicFreeSheaf
public import M9StacksIntegration.MukaiConormalRank
public import M9StacksIntegration.CurveKernelImage
public import M9StacksIntegration.CurveConstantRankFibers
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# The actual conormal-to-determinant-evaluation kernel on the curve

The morphism here is constructed from the original conormal inclusion,
the original primitive basis, and the actual third-exterior evaluation.
Its kernel is the genuine categorical kernel. On the smooth proper curve
it and its image are derived to be finite locally free, so the original
kernel inclusion splits locally. No constant-rank or cokernel-flatness
assumption is used, and no rank-one conclusion is claimed here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace M9Native.MukaiCubicCurveKernel

open MukaiPrimitiveCanonicalEvaluation MukaiCubicConstantSheaf MukaiConstantFreeBasis
open MukaiCubicFreeSheaf MukaiConormalBundle MukaiConormalEulerTwist
open LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0))
    (d : EvaluationDiagram K f E b)

abbrev curveSource : X.Modules := curveTwistedConormal K d.map

def curveFormMap : curveSource K f E b d ⟶ freeOn X 14 :=
  (Scheme.Modules.pullback d.map).map (twistedConormalMap K) ≫
    (pullbackFreeIso d.map 14).hom

def evaluationModuleMap : formModule K ⟶ ModuleCat.of K (DeterminantH0 K f E) :=
  ModuleCat.ofHom (primitiveEvaluation K f E b)

def curveEvaluationMap : curveSource K f E b d ⟶
    constantObj (.of K) f (ModuleCat.of K (DeterminantH0 K f E)) :=
  curveFormMap K f E b d ≫ (formsIso K f).inv ≫
    constantMap (.of K) f (evaluationModuleMap K f E b)

abbrev curveKernel : X.Modules := kernel (curveEvaluationMap K f E b d)

omit [CharZero K] in
theorem constantFinite_rank (M : ModuleCat.{u} K) [FiniteDimensional K M] :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (constantObj (.of K) f M) (finrank K M) := by
  let e := constantBasisIso (.of K) f M (finrank K M)
    ((Module.finBasis K M).reindex Equiv.ulift.symm)
  exact SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso e.symm
    (SheafOfModules.isFiniteLocallyFreeOfRank_free (R := X.ringCatSheaf) (finrank K M))

variable [IsAlgClosed K]

theorem curveSource_rank :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} (curveSource K f E b d) 7 := by
  let := MukaiConormalRank.twistedConormal_rank K
  exact isFiniteLocallyFreeOfRank_pullback _ _ 7

variable [IsCurve K f] [Smooth f] [IsProper f]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]

omit [CharZero K] [IsAlgClosed K] [IsCurve K f] [Smooth f] in
theorem determinantH0_finite : FiniteDimensional K (DeterminantH0 K f E) := by
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u}
      (Scheme.Modules.exteriorPower E (3 : ℤ)) 1 := by
    simpa using Scheme.Modules.isFiniteLocallyFreeOfRank_exteriorPower_self E 3
  let : (Scheme.Modules.exteriorPower E (3 : ℤ)).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank
      K f (Scheme.Modules.exteriorPower E (3 : ℤ)) 1
  exact finiteDimensional_cohomologyOverField_of_isProper K f
    (Scheme.Modules.exteriorPower E (3 : ℤ)) 0

theorem curveKernel_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (curveKernel K f E b d) := by
  let := determinantH0_finite K f E
  have hF := (curveSource_rank K f E b d).isFiniteLocallyFree
  have hG := (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))).isFiniteLocallyFree
  exact CurveKernelImage.kernel_isFiniteLocallyFree (isRegular_of_smooth_over_field f)
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
    (curveEvaluationMap K f E b d) hF hG

theorem curveKernel_sequence_locally_split (x : X) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty ((CurveKernelImage.sequence (curveEvaluationMap K f E b d)).map
        (Scheme.Modules.restrictFunctor U.ι)).Splitting := by
  let := determinantH0_finite K f E
  have hF := (curveSource_rank K f E b d).isFiniteLocallyFree
  have hG := (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))).isFiniteLocallyFree
  exact CurveKernelImage.sequence_locally_split (isRegular_of_smooth_over_field f)
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
    (curveEvaluationMap K f E b d) hF hG x

theorem curveImage_isFiniteLocallyFree :
    SheafOfModules.IsFiniteLocallyFree.{u,u,u} (image (curveEvaluationMap K f E b d)) := by
  let := determinantH0_finite K f E
  have hF := (curveSource_rank K f E b d).isFiniteLocallyFree
  have hG := (constantFinite_rank K f (ModuleCat.of K (DeterminantH0 K f E))).isFiniteLocallyFree
  exact CurveKernelImage.image_isFiniteLocallyFree (isRegular_of_smooth_over_field f)
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := f)))
    (curveEvaluationMap K f E b d) hF hG

/-- The original categorical kernel inclusion stays injective on every
actual residue fiber, using its derived locally free image quotient. -/
theorem curveKernel_fiber_injective (x : X) :
    Function.Injective (TupleEvaluationFiber.inducedFiberMap
      (kernel.ι (curveEvaluationMap K f E b d)) x) :=
  CurveConstantRankFibers.fiberMap_injective_of_shortExact
    (CurveKernelImage.sequence (curveEvaluationMap K f E b d))
    (CurveKernelImage.sequence_shortExact (curveEvaluationMap K f E b d))
    (curveImage_isFiniteLocallyFree K f E b d) x

end M9Native.MukaiCubicCurveKernel
