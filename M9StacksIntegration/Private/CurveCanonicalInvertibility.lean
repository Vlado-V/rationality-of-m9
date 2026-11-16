module

public import M9StacksIntegration.CurveClosedPointDimension
public import M9StacksIntegration.Private.GorensteinCanonicalHomology
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingComplex
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.Regular
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StalkwiseInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineOfModuleCategory
public import StacksFrontier.RingTheory.Dualizing.GorensteinCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.ClosedImmersionNormalizedStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModel
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtensionInvertibleGlobal

/-!
# The actual canonical module of a smooth proper curve is invertible

Selected native Gorenstein/normalized-stalk proof from pinned Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b,
`AlgebraicGeometry/Curves/GenusCurve/DualizingDegree.lean`.
The audit binds the original source hash and namespace changes. This
private isolated port includes only canonical invertibility: the actual
proper-over-field dualizing complex and its actual normalized derived
stalks are proved by native providers. Local dimension at closed points
comes from the checked integral-curve coheight lemma, avoiding the
projective-completion dependency. No canonical degree is assumed.
-/

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

universe u

namespace M9Native.CurveCanonicalInvertibility

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Duality

/-- The actual right-adjoint complex is dualizing, by the native
proper-over-field affine-chart construction. -/
theorem actualComplex_isDualizing {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] :
    letI := LocallyOfFiniteType.isLocallyNoetherian f
    Stacks.Duality.IsDualizingComplex (dualizingComplexOverField f).obj := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let : IsNoetherian X := {}
  exact ProperOverField.isDualizingComplex_of_charts (ProperOverField.hasCharts f)

/-- The native actual derived stalk of the actual proper-over-field
right-adjoint complex is normalized at every original closed point. -/
theorem actualComplex_stalk_normalized {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI := HasDerivedCategory.standard X.Modules
    letI := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
    Dualizing.IsNormalizedDualizingComplex.{u, 0}
      ((derivedStalkFunctor x).obj (dualizingComplexOverField f).obj) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  obtain ⟨ω, hω⟩ := actualComplex_isDualizing f U hU
  have h0 := ProperOverField.associatedShiftFunction_eq_zero_of_charts
    (ProperOverField.hasCharts f) x hx
  have h1 := associatedShiftFunction_eq_dualizingDimension hU ω hω x hxU
  exact (isNormalizedDualizingComplex_derivedStalkFunctor_iff _ hU ω
    ((isDualizingModelOn_standard_iff _ hU ω).2 hω) x hxU).2 (h1.symm.trans h0)

attribute [local instance high] HasDerivedCategory.standard

/-- Smoothness of the actual curve supplies canonical invertibility;
no determinant bundle or desired line-bundle property is a premise. -/
theorem dualizing_isInvertible {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (dualizingSheafOverField f) := by
  let : IsGorenstein X := isGorenstein_of_isRegular X (isRegular_of_smooth_over_field f)
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact Stacks.UFDExtensionGlobal.isInvertible_of_iso
    (homologyModelIso (dualizingComplexOverField f).obj (-1))
    (GorensteinCanonicalHomology.homology_neg_one_isInvertible k f (IsCurve.topologicalKrullDim_eq_one f).le
      (fun x hx => CurveClosedPointDimension.ringKrullDim_stalk_eq_one f x hx) _
      ((isDualizingComplex_standard_iff _).2 (actualComplex_isDualizing f))
      (fun x hx => actualComplex_stalk_normalized f x hx))

end M9Native.CurveCanonicalInvertibility
