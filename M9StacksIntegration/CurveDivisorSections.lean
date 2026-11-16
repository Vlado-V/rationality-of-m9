module

public import M9StacksIntegration.LinearSeriesAddEffectiveDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Restriction of an actual line bundle to a finite curve divisor

The restriction has as many sections as the length of the original
finite subscheme, including nonreduced subschemes. Its original ideal
sequence bounds the loss of global sections when twisting down.
No decomposition into rational points is required.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CurveDivisorSections

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open M9StacksIntegration.InvertibleHomCancellation (tensorRight)
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]

/-- Every actual line bundle on a finite zero-dimensional closed
subscheme has the same `H⁰` dimension as its structure sheaf. -/
theorem finiteRestriction_cohomology_zero_finrank
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k (cohomologyOverField k (D.subschemeι ≫ f)
      ((Scheme.Modules.pullback D.subschemeι).obj L) 0) =
        Module.finrank k Γ(D.subscheme, ⊤) := by
  let : DiscreteTopology (D.subscheme : Type u) :=
    Stacks.AlgebraicGeometry.ComponentDegrees.discreteTopology_of_isProper_of_topologicalKrullDim_le_zero
      k (D.subschemeι ≫ f) hD
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  let : Stacks.SheafOfModules.IsInvertible D.subscheme.presheaf
      D.subscheme.ringCatSheaf.property ((Scheme.Modules.pullback D.subschemeι).obj L) :=
    Stacks.InvertibleBridge.stacksIsInvertible_of_algebraicGeometryIsInvertible
  obtain ⟨e⟩ := Stacks.SheafOfModules.nonempty_iso_unit_of_discreteTopology D.subscheme
    ((Scheme.Modules.pullback D.subschemeι).obj L)
  exact (finrank_cohomologyOverField_eq_of_iso k (D.subschemeι ≫ f) e 0).trans
    (finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k (D.subschemeι ≫ f))

/-- The same dimension statement at the actual pushforward appearing in
the restriction short exact sequence. -/
theorem finiteRestrictionPushforward_cohomology_zero_finrank
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L)) 0) =
        Module.finrank k Γ(D.subscheme, ⊤) :=
  (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k D.subschemeι f _ 0).symm.trans
    (finiteRestriction_cohomology_zero_finrank f D hD L)

/-- The original negative-divisor twist, with the orientation of the
native exact ideal sequence. -/
abbrev twistDown (D : X.IdealSheafData) (L : X.Modules) : X.Modules :=
  (tensorRight L).obj (Stacks.Divisors.idealSheafOfModules D)

instance twistDown_isInvertible (D : X.IdealSheafData) [hD : IsEffectiveCartierDivisor D]
    (L : X.Modules) [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property (twistDown D L) := by
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property
      (Stacks.Divisors.idealSheafOfModules D) := hD
  let : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L hL
  exact Stacks.SheafOfModules.tensorProduct_isInvertible X.presheaf X.ringCatSheaf.property
    (Stacks.Divisors.idealSheafOfModules D) L

/-- The original inclusion `I_D ⊗ L → L`. -/
def twistDownι (D : X.IdealSheafData) (L : X.Modules) : twistDown D L ⟶ L :=
  (tensorRight L).map (Stacks.Divisors.idealInclusion D) ≫
    (Stacks.Divisors.tensorUnitIso L).hom

/-- The original adjunction unit restricting L to D. -/
def restrictionπ (D : X.IdealSheafData) (L : X.Modules) :
    L ⟶ (Scheme.Modules.pushforward D.subschemeι).obj
      ((Scheme.Modules.pullback D.subschemeι).obj L) :=
  (Scheme.Modules.pullbackPushforwardAdjunction D.subschemeι).unit.app L

def restrictionSequence (D : X.IdealSheafData) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    ShortComplex X.Modules :=
  ShortComplex.mk (twistDownι D L) (restrictionπ D L)
    (Stacks.Divisors.exists_shortExact_invertibleTwist D L hL).choose

theorem restrictionSequence_shortExact (D : X.IdealSheafData) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    (restrictionSequence D L).ShortExact :=
  (Stacks.Divisors.exists_shortExact_invertibleTwist D L hL).choose_spec

/-- Properness supplies finiteness of the actual line-bundle section
space, including the case where it is zero. -/
theorem invertible_cohomology_zero_finite (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    Module.Finite k (cohomologyOverField k f L 0) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : L.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  exact finiteDimensional_cohomologyOverField_of_isProper k f L 0

/-- Rank-nullity for the original restriction map, with its kernel
identified by the actual ideal short exact sequence. -/
theorem restriction_range_finrank_add_twistDown (D : X.IdealSheafData) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L] :
    Module.finrank k (LinearMap.range (cohomologyOverFieldMap k f (restrictionπ D L) 0).hom) +
      Module.finrank k (cohomologyOverField k f (twistDown D L) 0) =
        Module.finrank k (cohomologyOverField k f L 0) := by
  let := invertible_cohomology_zero_finite f L
  obtain ⟨_δ, hi, he, _hd, _hd'⟩ :=
    exists_cohomologyOverField_longExactSequence k f (restrictionSequence_shortExact D L)
  let a := (cohomologyOverFieldMap k f (twistDownι D L) 0).hom
  let q := (cohomologyOverFieldMap k f (restrictionπ D L) 0).hom
  have ha : Function.Injective a := hi
  have hex : Function.Exact a q := he 0
  have hr := q.finrank_range_add_finrank_ker
  rw [hex.linearMap_ker_eq, LinearMap.finrank_range_of_inj ha] at hr
  exact hr

/-- Twisting down by a positive-length finite divisor loses at most its
actual length in global sections. -/
theorem cohomology_zero_le_twistDown_add_length
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (d : ℕ) (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = d) (hpos : 0 < d) :
    Module.finrank k (cohomologyOverField k f L 0) ≤
      Module.finrank k (cohomologyOverField k f (twistDown D L) 0) + d := by
  have hq : Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L)) 0) = d :=
    (finiteRestrictionPushforward_cohomology_zero_finrank f D hD L).trans hd
  let := Module.finite_of_finrank_pos (R := k) (by rw [hq]; exact hpos)
  have hle := Submodule.finrank_le
    (LinearMap.range (cohomologyOverFieldMap k f (restrictionπ D L) 0).hom)
  have hr := restriction_range_finrank_add_twistDown f D L
  omega

/-- If a three-dimensional complete system fails to restrict onto a
length-two subscheme, at least two of its sections survive in the actual
negative twist. -/
theorem two_le_twistDown_h0_of_restriction_not_surjective
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (hL : Module.finrank k (cohomologyOverField k f L 0) = 3)
    (hnot : ¬ Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D L) 0)) :
    2 ≤ Module.finrank k (cohomologyOverField k f (twistDown D L) 0) := by
  have hq : Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L)) 0) = 2 :=
    (finiteRestrictionPushforward_cohomology_zero_finrank f D hD L).trans hd
  let := Module.finite_of_finrank_pos (R := k) (by rw [hq]; decide)
  let q := (cohomologyOverFieldMap k f (restrictionπ D L) 0).hom
  have hrange : LinearMap.range q ≠ ⊤ := fun h => hnot (LinearMap.range_eq_top.mp h)
  have hlt := Submodule.finrank_lt hrange
  have hr := restriction_range_finrank_add_twistDown f D L
  change Module.finrank k (LinearMap.range q) + _ = _ at hr
  omega

/-- A length-two restriction is onto if the original system has at
least three sections and the actual negative twist has at most one. -/
theorem restriction_surjective_of_three_le_h0_of_twistDown_h0_le_one
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2)
    (hL : 3 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (hI : Module.finrank k (cohomologyOverField k f (twistDown D L) 0) ≤ 1) :
    Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D L) 0) := by
  have hq : Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward D.subschemeι).obj
        ((Scheme.Modules.pullback D.subschemeι).obj L)) 0) = 2 :=
    (finiteRestrictionPushforward_cohomology_zero_finrank f D hD L).trans hd
  let := Module.finite_of_finrank_pos (R := k) (by rw [hq]; decide)
  let q := (cohomologyOverFieldMap k f (restrictionπ D L) 0).hom
  have hr := restriction_range_finrank_add_twistDown f D L
  change Module.finrank k (LinearMap.range q) + _ = _ at hr
  by_contra hnot
  have hrange : LinearMap.range q ≠ ⊤ := fun h => hnot (LinearMap.range_eq_top.mp h)
  have hlt := Submodule.finrank_lt hrange
  omega

end M9Native.CurveDivisorSections
