module

public import M9StacksIntegration.CurveDivisorSections
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.TorsionFreeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Divisors.TorsionFree.Submodule
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular

/-!
# Finite subschemes of an actual smooth curve are Cartier divisors

The original ideal is coherent and torsion free as a submodule of the
structure sheaf. On a regular integral curve it is therefore finite
locally free. The zero-dimensional subscheme misses the original
generic point, where the ideal sequence proves that its fibre rank is
one. Constancy of rank then gives actual invertibility of the ideal.

This supplies the effective Cartier property for arbitrary length-two
subschemes, including nonreduced ones, using the already checked native
torsion-free and constant-rank theorems.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.FiniteCurveDivisor

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules

/-- A zero-dimensional closed subscheme of a one-dimensional integral
scheme misses its actual generic point. -/
theorem genericPoint_notMem_range_of_dimension_zero {X : Scheme.{u}} [IsIntegral X]
    (hdim : topologicalKrullDim X = 1) (D : X.IdealSheafData)
    (hD : topologicalKrullDim D.subscheme ≤ 0) :
    genericPoint X ∉ Set.range D.subschemeι.base := by
  intro h
  have hcl : IsClosed (Set.range D.subschemeι.base) :=
    D.subschemeι.isClosedEmbedding.isClosed_range
  have huniv : Set.range D.subschemeι.base = Set.univ := by
    by_contra hne
    exact notMem_of_isClosed_of_ne_univ _ hcl hne h
  have hhomeo : IsHomeomorph D.subschemeι.base :=
    (isHomeomorph_iff_isEmbedding_surjective).mpr
      ⟨D.subschemeι.isClosedEmbedding.isEmbedding, Set.range_eq_univ.mp huniv⟩
  have heq := hhomeo.topologicalKrullDim_eq
  rw [heq, hdim] at hD
  exact absurd hD (by norm_num)

/-- The actual ideal module of any closed subscheme of a locally
Noetherian scheme is coherent, by its actual kernel presentation. -/
theorem idealModule_isCoherent {X : Scheme.{u}} [IsLocallyNoetherian X]
    (D : X.IdealSheafData) : (Stacks.Divisors.negativeTwist' D).IsCoherent := by
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  let : ((RingedSpaceModuleAdjunction.modulePushforward D.subschemeι.toLRSHom.toShHom).obj
      (SheafOfModules.unit (structureSheafRing D.subscheme.toRingedSpace))).IsCoherent :=
    Stacks.Chow.isCoherent_pushforwardStructureSheaf D.subschemeι
  exact AlgebraicGeometry.CoherentAbelian.isCoherent_kernel
    (Stacks.IdealSheafSequence.divisorQuotientMap D)

/-- The original ideal of a finite subscheme on an actual regular
integral curve is finite locally free. -/
theorem idealModule_isFiniteLocallyFree {X : Scheme.{u}} [IsIntegral X]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) :
    SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf)
      (Stacks.Divisors.negativeTwist' D) := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.structureSheaf_isCoherent X
  let : (Stacks.Divisors.negativeTwist' D).IsCoherent := idealModule_isCoherent D
  have hunit : IsTorsionFree (SheafOfModules.unit X.ringCatSheaf : X.Modules) := by
    apply (isTorsionFree_iff_isFiniteLocallyFree hreg hdim _).mpr
    exact (SheafOfModules.isFiniteLocallyFreeOfRank_one_of_isInvertible X
      (SheafOfModules.unit X.ringCatSheaf)).isFiniteLocallyFree
  have htf : IsTorsionFree (Stacks.Divisors.negativeTwist' D : X.Modules) := by
    apply isTorsionFree_of_injective_app (Stacks.IdealSheafSequence.divisorIdealMap D) ?_ hunit
    intro U
    exact (ModuleCat.mono_iff_injective _).mp
      (inferInstance : Mono ((SheafOfModules.evaluation X.ringCatSheaf (op U)).map
        (Stacks.IdealSheafSequence.divisorIdealMap D)))
  exact (isTorsionFree_iff_isFiniteLocallyFree hreg hdim _).mp htf

/-- The original ideal has rank one at the original generic point,
deduced from its exact ideal sequence and the support of the quotient. -/
theorem idealModule_generic_fiberRank_eq_one {X : Scheme.{u}} [IsIntegral X]
    (hreg : IsRegular X) (hdim : topologicalKrullDim X = 1)
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0) :
    Scheme.Modules.fiberRank (Stacks.Divisors.negativeTwist' D) (genericPoint X) = 1 := by
  let : IsLocallyNoetherian X := isLocallyNoetherian_of_isRegular hreg
  let I : X.Modules := Stacks.Divisors.negativeTwist' D
  let : I.IsCoherent := idealModule_isCoherent D
  let : I.IsFiniteType := SheafOfModules.IsCoherent.isFiniteType
  obtain ⟨w, hS⟩ := Stacks.IdealSheafSequence.divisorIdeal_shortExact D
  let S : ShortComplex X.Modules := ShortComplex.mk
    (Stacks.IdealSheafSequence.divisorIdealMap D)
    (Stacks.IdealSheafSequence.divisorQuotientMap D) w
  have hS' : S.ShortExact := hS
  have hfield : IsField (X.presheaf.stalk (genericPoint X)) :=
    (inferInstance : Field X.functionField).toIsField
  have hlen : Module.length (X.presheaf.stalk (genericPoint X))
      (S.X₂.presheaf.stalk (genericPoint X)) =
      Module.length (X.presheaf.stalk (genericPoint X))
        (S.X₁.presheaf.stalk (genericPoint X)) +
      Module.length (X.presheaf.stalk (genericPoint X))
        (S.X₃.presheaf.stalk (genericPoint X)) := by
    obtain ⟨a, b, ha, hab, hb⟩ :=
      Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS' (genericPoint X)
    exact Module.length_eq_add_of_exact a b ha hb hab
  have lengthRank (M : X.Modules) [M.IsFiniteType] :
      (Module.length (X.presheaf.stalk (genericPoint X))
        (M.presheaf.stalk (genericPoint X))).toNat =
          Scheme.Modules.fiberRank M (genericPoint X) := by
    let : Field (X.presheaf.stalk (genericPoint X)) := hfield.toField
    let : Module.Finite (X.presheaf.stalk (genericPoint X))
        (M.presheaf.stalk (genericPoint X)) :=
      SheafOfModules.finite_stalk X.sheaf M (genericPoint X)
    rw [Module.length_eq_finrank,
      Scheme.Modules.fiberRank_eq_finrank_stalk M (genericPoint X)
        (Module.Free.of_divisionRing _ _)]
    simp
  have hI := lengthRank I
  have hO := lengthRank (structureSheafModule X)
  rw [Scheme.Modules.fiberRank_unit_eq_one] at hO
  have hnot : genericPoint X ∉ SheafOfModules.supp ((Scheme.Modules.pushforward
      D.subschemeι).obj (SheafOfModules.unit D.subscheme.ringCatSheaf)) := by
    rw [Stacks.Chow.supp_pushforwardStructureSheaf]
    exact genericPoint_notMem_range_of_dimension_zero hdim D hD
  have hz (M : X.Modules) (hM : genericPoint X ∉ SheafOfModules.supp M) :
      Module.length (X.presheaf.stalk (genericPoint X))
        (M.presheaf.stalk (genericPoint X)) = 0 := by
    have hzero (a : M.presheaf.stalk (genericPoint X)) : a = 0 := by
      by_contra ha
      exact hM ⟨a, ha⟩
    let : Subsingleton (M.presheaf.stalk (genericPoint X)) :=
      ⟨fun a b => (hzero a).trans (hzero b).symm⟩
    exact Module.length_eq_zero
  have hQ := hz S.X₃ hnot
  rw [hQ, add_zero] at hlen
  change Scheme.Modules.fiberRank I (genericPoint X) = 1
  rw [← hI]
  exact (congrArg ENat.toNat hlen.symm).trans hO

/-- Every actual zero-dimensional closed subscheme of an actual regular
integral one-dimensional scheme is an effective Cartier divisor. -/
theorem isEffectiveCartierDivisor_of_regular_dimension_one
    {X : Scheme.{u}} [IsIntegral X] (hreg : IsRegular X)
    (hdim : topologicalKrullDim X = 1) (D : X.IdealSheafData)
    (hD : topologicalKrullDim D.subscheme ≤ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor D := by
  let := idealModule_isFiniteLocallyFree hreg hdim.le D
  exact Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Scheme.Modules.isInvertible_of_fiberRank_eq_one (Stacks.Divisors.negativeTwist' D)
      (genericPoint X) (idealModule_generic_fiberRank_eq_one hreg hdim D hD))

/-- In particular the actual smooth-curve hypotheses supply the Cartier
property needed for arbitrary length-two tests. -/
theorem isEffectiveCartierDivisor_of_dimension_zero
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [IsCurve k f] [Smooth f] (D : X.IdealSheafData)
    (hD : topologicalKrullDim D.subscheme ≤ 0) :
    Stacks.Divisors.IsEffectiveCartierDivisor D :=
  isEffectiveCartierDivisor_of_regular_dimension_one (isRegular_of_smooth_over_field f)
    (IsCurve.topologicalKrullDim_eq_one f) D hD

end M9Native.FiniteCurveDivisor
