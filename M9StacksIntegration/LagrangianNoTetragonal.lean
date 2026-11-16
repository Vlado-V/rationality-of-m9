module

public import M9StacksIntegration.LagrangianMovingFourCommonSection
public import M9StacksIntegration.LagrangianSectionZeroBoundApplications
public import M9StacksIntegration.FiniteClosedSectionH0
public import M9StacksIntegration.LagrangianTransverseSixSections

/-! The actual four distinct points of the original pencil fibre lie
in one SAME FULL native quotient-section zero scheme. Their reduced
divisor is an actual closed subscheme of that full zero scheme, so
its genuine original-field H0 dimension four contradicts the full
section-zero bound two. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Module
universe u

namespace M9Native.LagrangianNoTetragonal

open PencilFourPointFibre LagrangianPencilFibreTripleRank
open LagrangianUniversalSections LagrangianHyperplaneEvaluation

variable (K : Type u) [Field K] [IsAlgClosed K]

/-- Actual maps of all four original fibre points into the same full
closed subscheme give the genuine ideal containment. -/
theorem ideal_le_reduced_fibre_of_factors
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f]
    (D : FourPointFibre K f) (J : X.IdealSheafData)
    (hfac : ∀ i, ∃ t : Spec (.of K) ⟶ J.subscheme,
      t ≫ J.subschemeι = curvePoint D i) :
    J ≤ RationalPointDivisor.divisor (closedPoint D) := by
  apply (RationalPointDivisorRestriction.ideal_le_divisor_iff f (closedPoint D) J).mpr
  intro i
  have hp : (((pointEquivClosedPoint f).symm (closedPoint D i)).val) = curvePoint D i := by
    exact congrArg Subtype.val ((pointEquivClosedPoint f).symm_apply_apply
      ⟨curvePoint D i, curvePoint_overBase D i⟩)
  rw [hp]
  obtain ⟨t,ht⟩ := hfac i
  have hk := Scheme.Hom.le_ker_comp t J.subschemeι
  rwa [Scheme.IdealSheafData.ker_subschemeι, ht] at hk

/-- The actual reduced four-point divisor embeds in the SAME finite
full closed subscheme. Native affine restriction and the original
structural K-action therefore force H0 dimension at least four. -/
theorem four_le_H0_of_full_fibre_factors
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f]
    (D : FourPointFibre K f) (J : X.IdealSheafData) [IsFinite (J.subschemeι ≫ f)]
    (hfac : ∀ i, ∃ t : Spec (.of K) ⟶ J.subscheme,
      t ≫ J.subschemeι = curvePoint D i) :
    4 ≤ finrank K (structureSheafCohomology (J.subschemeι ≫ f) 0) := by
  have hmono := FiniteClosedSectionH0.h0_le_of_ideal_le K f J
    (RationalPointDivisor.divisor (closedPoint D))
    (ideal_le_reduced_fibre_of_factors K f D J hfac)
  have hfour : finrank K (structureSheafCohomology
      ((RationalPointDivisor.divisor (closedPoint D)).subschemeι ≫ f) 0) = 4 := by
    rw [FiniteClosedSectionH0.structureH0_finrank_eq_functions K]
    exact RationalPointDivisor.length_eq (closedPoint D) f (closedPoint_injective D)
  rwa [hfour] at hmono

/-- The original integral smooth transverse LG cut has no degree-four
pencil. Its genus, canonical completeness, point ranks, common section,
full zero scheme, finiteness and length contradiction are all derived. -/
theorem no_g1_four_at_dimension [CharZero K]
    (M : Matrix (Fin 5) (Fin 14) K)
    [IsIntegral (LagrangianTransverseRestriction.curve K M)]
    [SmoothOfRelativeDimension 1 (LagrangianTransverseRestriction.curveProjection K M)]
    (hM : Function.Surjective M.mulVec)
    (hdim : topologicalKrullDim (LagrangianTransverseRestriction.curve K M) ≤ 1) :
    ¬ Nonempty (LinearSeries K (LagrangianTransverseRestriction.curveProjection K M) hdim 4 1) := by
  rintro ⟨A⟩
  obtain ⟨D,v,hv,_hzero,hfac⟩ :=
    LagrangianMovingFourCommonSection.exists_original_pencil_fibre_common_section K M hM hdim A
  let f := LagrangianTransverseRestriction.curveProjection K M
  let l := LagrangianTransverseRestriction.inclusion K M
  let : SheafOfModules.IsFiniteLocallyFree.{u,u,u} (bundle K l) :=
    bundle_finiteLocallyFree K l
  let : IsFinite (zeroProjection K f l v) :=
    NonzeroSectionZeroFinite.isFinite_zeroSchemeOfSection_of_dimension_le_one
      (bundle K l) (originalSection K f l v) K f hdim
      (LagrangianTransverseSixSections.quotient_constantVector_ne_zero K M hM v hv)
  have hfour := four_le_H0_of_full_fibre_factors K f D (zeroIdeal K f l v) hfac
  have htwo : finrank K (structureSheafCohomology
      ((zeroIdeal K f l v).subschemeι ≫ f) 0) ≤ 2 :=
    LagrangianSectionZeroBoundApplications.ordered_zero_H0_le_two K M hM v hv
  omega

end M9Native.LagrangianNoTetragonal
