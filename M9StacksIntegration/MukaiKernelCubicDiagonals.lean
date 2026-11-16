module

public import M9StacksIntegration.MukaiKernelCubicFieldValues
public import M9StacksIntegration.MukaiCubicPositivePoint
public import M9StacksIntegration.MukaiCurvePointLineValues
public import M9StacksIntegration.MukaiConormalFieldAvoidance

/-! The original kernel cubic has actual inverse-determinant-line
diagonal values at every genuine same-base field point. Actual Semi3
also makes these values nonzero for nonzero original kernel sections.
No line-valued cubic or nondegenerate fibre is supplied as an input. -/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
open Stacks.AlgebraicGeometry.ReflexiveModules

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Hom
  Stacks.SheafOfModules.Tensor.ringSheaf

universe u

namespace M9Native.MukaiKernelCubicDiagonals

open MukaiPrimitiveCanonicalEvaluation MukaiCubicCurveKernel MukaiCurvePointCoordinates
open MukaiCubicFreeSheaf MukaiKernelCubicFieldValues MukaiEvaluationPointFrame
open MukaiConormalOriginFrame LagrangianTranslatedCharts MukaiCubicPositivePoint
open MukaiQuarticGradientTransport MukaiConormalPrimitive MukaiFieldLineCubic
open MukaiCurvePointLine LagrangianMatrixChart AlgebraicGeometry.Grassmannian

variable (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (E : X.Modules)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u,u,u} E 3]
    (b : Basis (Fin 6) K (cohomologyOverField K f E 0)) (d : EvaluationDiagram K f E b)

/-- The preimage belongs to the actual pullback of the original curve
point line. It is constructed from the original quotient frame. -/
theorem diagonal_pointLine_preimage (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d))) :
    ∃ a : Γ((Scheme.Modules.pullback p).obj
      (dualSheaf (Scheme.Modules.exteriorPower E (3 : ℤ))), ⊤),
      (pointKernelCubic K f E b d p).app ⊤
        (tripleSection K ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) s s s) =
      (pullbackFreeIso p 14).hom.app ⊤
        (((Scheme.Modules.pullback p).map (curvePointLine K f E b d)).app ⊤ a) := by
  obtain ⟨g,e,hg,_hM,himage⟩ := exists_simultaneous_normal_form K f E b d p hp
  have hell : kernelFormsMap K f E b d p s ∈
      LinearMap.range (pointFormsMap K f E b d p) :=
    range_kernelFormsMap_le K f E b d p ⟨s,rfl⟩
  rw [himage] at hell
  obtain ⟨v,hv⟩ := hell
  change formsAction K g⁻¹ (conormalForm K v) = kernelFormsMap K f E b d p s at hv
  have hg' : p ≫ d.map = zeroPoint K ≫ translatedBigCell K g := by
    simpa only [origin, translatedBigCell, Category.assoc] using hg
  obtain ⟨a,ha⟩ := MukaiCurvePointLineValues.positivePoint_preimage K f E b d p g hg'
  refine ⟨(Scheme.ΓSpecIso (.of K)).inv.hom (4*v.2.val.det) • a,?_⟩
  rw [pointKernelCubic_diagonal K f E b d p hp, ← hv,
    primitiveCubic_translated_origin K g v.1 v.2,
    dualFormSection_smul, MukaiFreePullbackCoordinates.baseScalar_id]
  change (Scheme.ΓSpecIso (.of K)).inv.hom (4*v.2.val.det) •
    pointSection K (𝟙 (Spec (.of K)))
      (MukaiConormalPositivePoint.positivePoint K (zeroPoint K) g) = _
  rw [Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, ha]

variable [IsCurve K f] [Smooth f] [IsProper f]

/-- Nonvanishing is derived from actual Semi3 and the literal local
gradient coefficient 4 det(S), not assumed as a fibre condition. -/
theorem diagonal_ne_zero
    (hσ : ExteriorEvaluation.lambda K f E 2 (MukaiLagrangianMap.basisSigma K f E b) = 0)
    (hsemi : MukaiSemiIrreducible.CompleteSemiIrreducible K f E 3)
    (p : Spec (.of K) ⟶ X) (hp : p ≫ f = 𝟙 _)
    (s : moduleSpecΓFunctor.obj ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)))
    (hs : s ≠ 0) :
    (pointKernelCubic K f E b d p).app ⊤
      (tripleSection K ((Scheme.Modules.pullback p).obj (curveKernel K f E b d)) s s s) ≠ 0 := by
  obtain ⟨g,e,_hg,hM,himage⟩ := exists_simultaneous_normal_form K f E b d p hp
  have hell : kernelFormsMap K f E b d p s ∈
      LinearMap.range (pointFormsMap K f E b d p) :=
    range_kernelFormsMap_le K f E b d p ⟨s,rfl⟩
  rw [himage] at hell
  obtain ⟨v,hv⟩ := hell
  change formsAction K g⁻¹ (conormalForm K v) = kernelFormsMap K f E b d p s at hv
  have hv0 : v ≠ 0 := by
    intro hzero
    apply hs
    apply kernelFormsMap_injective K f E b d p
    simpa only [hzero, map_zero] using hv.symm
  have hker := MukaiCurveEvaluationPoint.kernelFormsMap_mem_evaluationKernel K f p hp E b d s
  have hdet := MukaiConormalFieldAvoidance.discriminant_ne_zero_of_evaluation_kernel
    K f E b hσ hsemi p hp g e hM v hv0 (by rw [hv]; exact hker)
  rw [pointKernelCubic_diagonal K f E b d p hp, ← hv]
  intro hzero
  have hpure : MukaiPrimitiveQuartic.primitiveCubic K
      (formsAction K g⁻¹ (conormalForm K v))
      (formsAction K g⁻¹ (conormalForm K v))
      (formsAction K g⁻¹ (conormalForm K v)) = 0 :=
    dualFormSection_injective K (𝟙 (Spec (.of K)))
      (hzero.trans (dualFormSection_zero K (𝟙 (Spec (.of K)))).symm)
  exact primitiveCubic_transformed_conormalForm_ne_zero K g⁻¹ v.1 v.2 hdet hpure

end M9Native.MukaiKernelCubicDiagonals
