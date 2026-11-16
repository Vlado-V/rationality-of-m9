module

public import M9StacksIntegration.MukaiBundleUniqueness
public import M9StacksIntegration.MukaiPencilDegreeBounds
public import StacksFrontier.AlgebraicGeometry.Curves.PointTwistDown
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.OverField

/-!
# Actual section bounds in the uniqueness argument

These statements use actual invertible sheaves, actual native cohomology,
and the absence of an actual degree-five pencil. No Clifford-index or
section-bound hypothesis is added to the underlying curve.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace M9Native.MukaiTwistBounds

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The restriction to a point which meets a nonzero section is onto its
one-dimensional actual `H⁰`, without an `H¹` vanishing hypothesis. -/
theorem H0_add_one_of_nonzero_point_restriction
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [Module.Finite k (cohomologyOverField k f S.X₂ 0)]
    (hone : Module.finrank k (cohomologyOverField k f S.X₃ 0) = 1)
    {a : cohomologyOverField k f S.X₂ 0}
    (ha : cohomologyOverFieldMap k f S.g 0 a ≠ 0) :
    Module.finrank k (cohomologyOverField k f S.X₁ 0) + 1 =
      Module.finrank k (cohomologyOverField k f S.X₂ 0) := by
  let v := (cohomologyOverFieldMap k f S.g 0).hom
  have hv : Function.Surjective v := by
    intro y
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hone ha y
    exact ⟨c • a, by simpa only [map_smul] using hc⟩
  have hu := MukaiCohomologyParity.cohomologyBoundary_injective_left k f hS
  have he := MukaiCohomologyParity.cohomologyBoundary_exact_left k f hS 0
  have hr := v.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hv, finrank_top, he.linearMap_ker_eq,
    LinearMap.finrank_range_of_inj hu, hone] at hr
  omega

/-- A genuine nonzero-section line bundle can be twisted down at an
actual closed point, dropping `h⁰` by one and strictly dropping its native
degree. Exact decrease of degree is unnecessary for the pencil bound. -/
theorem exists_lower_degree_one_less_H0 (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hpos : 2 ≤ Module.finrank k (cohomologyOverField k f L 0)) :
    ∃ (L' : X.Modules) (hL' : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L'),
      letI := hL'
      invertibleCurveDegree k f hdim L' < invertibleCurveDegree k f hdim L ∧
      Module.finrank k (cohomologyOverField k f L' 0) + 1 =
        Module.finrank k (cohomologyOverField k f L 0) := by
  obtain ⟨Z, i, hi, L', α, β, w, hSE, hL', hone, a, ha⟩ :=
    exists_pointTwistDown k f L hL (by omega)
  letI := hi
  letI : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L' := hL'
  letI : Module.Finite k (cohomologyOverField k f L 0) :=
    Module.finite_of_finrank_pos (by omega)
  have hone' : Module.finrank k (cohomologyOverField k f
      ((Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback i).obj L)) 0) = 1 :=
    (cohomologyOverFieldPushforwardIsoOfIsClosedImmersion k i f
      ((Scheme.Modules.pullback i).obj L) 0).toLinearEquiv.finrank_eq.symm.trans hone
  have hdrop := H0_add_one_of_nonzero_point_restriction f hSE hone' ha
  change Module.finrank k (cohomologyOverField k f L' 0) + 1 =
    Module.finrank k (cohomologyOverField k f L 0) at hdrop
  have hα : α ≠ 0 := by
    intro hz
    have hepi := hSE.epi_g
    letI := hSE.mono_f
    have hzero : CategoryTheory.Limits.IsZero L' :=
      CategoryTheory.Limits.IsZero.of_mono_eq_zero α hz
    letI : (cohomologyOverFieldFunctor k f 0).Additive := by
      dsimp [cohomologyOverFieldFunctor]
      infer_instance
    have hzH : IsZero (cohomologyOverField k f L' 0) :=
      (cohomologyOverFieldFunctor k f 0).map_isZero hzero
    letI := ModuleCat.subsingleton_of_isZero hzH
    have hz0 : Module.finrank k (cohomologyOverField k f L' 0) = 0 :=
      Module.finrank_zero_of_subsingleton
    omega
  have hdeg := invertibleCurveDegree_le_of_hom_ne_zero k f hdim L' L α hα
  refine ⟨L', hL', lt_of_le_of_ne hdeg ?_, hdrop⟩
  intro heq
  letI := isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero k f hdim L' L α hα heq
  have hd := (cohomologyOverFieldIso k f (asIso α) 0).toLinearEquiv.finrank_eq
  omega

/-- Absence of a degree-five pencil bounds sections of every actual
line bundle of degree at most five. Negative degrees are included. -/
theorem h0_le_one_of_degree_le_five
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L ≤ 5) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 1 := by
  by_contra hh
  have hh' : 2 ≤ Module.finrank k (cohomologyOverField k f L 0) := by omega
  have h6 := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp L hh'
  omega

/-- A degree-six net would yield a degree-at-most-five pencil by removing
an actual point. This avoids a Clifford-index assumption. -/
theorem h0_le_two_of_degree_le_six
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L ≤ 6) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 2 := by
  by_contra hh
  have hh' : 3 ≤ Module.finrank k (cohomologyOverField k f L 0) := by omega
  obtain ⟨L', hL', hdeg', hdrop⟩ := exists_lower_degree_one_less_H0 f hdim L (by omega)
  letI := hL'
  have hbound := h0_le_one_of_degree_le_five f hdim hnp L' (by omega)
  omega


end M9Native.MukaiTwistBounds
