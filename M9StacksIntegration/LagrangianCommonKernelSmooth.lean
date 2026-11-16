module

public import M9StacksIntegration.LagrangianCommonKernelChartIso
public import M9StacksIntegration.LagrangianTranslatedCharts

/-! Smoothness of the actual full first-quotient-section zero scheme.
The proof uses its frozen affine-three open cover and literal structure
maps, retaining the original native section-zero scheme. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
universe u

namespace M9Native.LagrangianCommonKernelSmooth

open LagrangianCommonKernelZero LagrangianCommonKernelChartIso
variable (K : Type u) [Field K] [CharZero K]

omit [CharZero K] in
/-- The original polynomial affine three-space has genuine smooth
relative dimension three over the original ground field. -/
theorem polynomialThree_smoothOfRelativeDimension :
    SmoothOfRelativeDimension 3
      (Spec.map (CommRingCat.ofHom (MvPolynomial.C (σ:=Fin 3) (R:=K)))) := by
  rw [HasRingHomProperty.Spec_iff (P:=@SmoothOfRelativeDimension 3)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap K (MvPolynomial (Fin 3) K)).IsStandardSmoothOfRelativeDimension 3
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algEquiv 3
    (MvPolynomial.renameEquiv K (Equiv.refl (Fin 3)))

/-- Smoothness follows on the actual four affine-three opens of the
full native zero scheme, without a model or dimension assumption. -/
instance smoothOfRelativeDimension_zeroProjection :
    SmoothOfRelativeDimension 3 (zeroProjection K) := by
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension 3 : MorphismProperty Scheme.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P:=@SmoothOfRelativeDimension 3)
    (affineThreeCover K) fun s => ?_
  change SmoothOfRelativeDimension 3
    (affineThreeMap K s.val s.property ≫ zeroProjection K)
  rw [affineThreeMap_projection]
  exact polynomialThree_smoothOfRelativeDimension K

instance smooth_zeroProjection : Smooth (zeroProjection K) :=
  SmoothOfRelativeDimension.smooth 3 (zeroProjection K)

end M9Native.LagrangianCommonKernelSmooth
