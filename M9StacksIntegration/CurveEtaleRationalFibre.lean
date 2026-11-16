module

public import M9StacksIntegration.CurveGenericResidueSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitz
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# Actual rational étale fibres of a nonconstant characteristic-zero curve map

Generic separability supplies an actual source open on which the map is
étale. The image of its closed complement is closed and misses the target
generic point: a point of a proper closed subset of an integral curve is
closed, and a finite map sends closed points to closed points. A genuine
closed point in the remaining target open is an original-field rational
point. Its full actual fibre is étale by the restriction pullback square.

Reducedness or an étale fibre is never supplied as a premise.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.CurveEtaleRationalFibre

/-- A genuine one-dimensional integral curve has a nonclosed generic point.
This is the short dimension argument used in native
`Curves/ZetaFunction/TwistedFrobeniusFixedPoints.ne_genericPoint_of_isClosed`. -/
theorem genericPoint_not_closed (K : Type u) [Field K] {Y : Scheme.{u}}
    (fY : Y ⟶ Spec (.of K)) [IsCurve K fY] :
    ¬ IsClosed ({genericPoint Y} : Set Y) := by
  intro h
  have hu : (Set.univ : Set Y) = {genericPoint Y} := by
    rw [← h.closure_eq]
    exact (genericPoint_spec Y).symm
  let : Subsingleton Y := ⟨fun a b => by
    have ha : a ∈ ({genericPoint Y} : Set Y) := hu ▸ Set.mem_univ a
    have hb : b ∈ ({genericPoint Y} : Set Y) := hu ▸ Set.mem_univ b
    rw [Set.mem_singleton_iff] at ha hb
    exact ha.trans hb.symm⟩
  have h1 := IsCurve.topologicalKrullDim_eq_one (k := K) (f := fY)
  have h0 := topologicalKrullDim_zero_of_discreteTopology Y
  rw [h1] at h0
  exact absurd h0 (by decide)

variable (K : Type u) [Field K] [IsAlgClosed K] [CharZero K]
  {X Y : Scheme.{u}} (fX : X ⟶ Spec (.of K)) (fY : Y ⟶ Spec (.of K))
  [IsCurve K fX] [IsCurve K fY] [IsProper fX] [IsProper fY]
  [Smooth fX] [Smooth fY]
  (g : X ⟶ Y) (hg : g ≫ fY = fX)
  (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y)

include hg hnc

/-- The original map has a genuinely constructed rational étale full fibre. -/
theorem exists_etale_fibre :
    ∃ q : Spec (.of K) ⟶ Y, q ≫ fY = 𝟙 _ ∧
      Etale (pullback.snd g q) := by
  classical
  let : IsFinite g := isFinite_of_not_constant K fX fY g hg hnc
  let : IsNoetherian X := isNoetherian_of_locallyOfFiniteType fX
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace fY
  obtain ⟨U,hU,hEtale⟩ := ((genericallyEtale_tfae fX fY g hg).out 5 4 rfl rfl).mp
    (CurveGenericResidueSeparable.generic_finite_separable_of_nonconstant fX fY g hg hnc)
  let := hEtale
  have hUne : (U : Set X)ᶜ ≠ Set.univ := by
    obtain ⟨u⟩ := hU
    intro h
    have hu : u.1 ∈ (U : Set X)ᶜ := h.symm ▸ Set.mem_univ u.1
    exact hu u.2
  have hclosed : IsClosed (g '' (U : Set X)ᶜ) := g.isClosedMap _ U.isOpen.isClosed_compl
  have hη : genericPoint Y ∉ g '' (U : Set X)ᶜ := by
    rintro ⟨x,hx,hxy⟩
    have hxclosed := Stacks.Topology.Dimension.isClosed_singleton_of_mem_of_ne_univ
      (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fX)).le
      U.isOpen.isClosed_compl hUne hx
    have hyclosed : IsClosed ({g x} : Set Y) := by
      simpa only [Set.image_singleton] using g.isClosedMap ({x} : Set X) hxclosed
    exact genericPoint_not_closed K fY (hxy ▸ hyclosed)
  let V : Y.Opens := ⟨(g '' (U : Set X)ᶜ)ᶜ,hclosed.isOpen_compl⟩
  have hV : (V : Set Y).Nonempty := ⟨genericPoint Y,hη⟩
  have hpre : g ⁻¹ᵁ V ≤ U := by
    intro x hx
    by_contra hxU
    exact hx ⟨x,hxU,rfl⟩
  have hcomp : Etale ((g ∣_ V) ≫ V.ι) := by
    rw [morphismRestrict_ι, ← X.homOfLE_ι hpre, Category.assoc]
    infer_instance
  let := hcomp
  let : Etale (g ∣_ V) := Etale.of_comp (g ∣_ V) V.ι
  obtain ⟨y,hyV,hyclosed⟩ := nonempty_inter_closedPoints hV V.isOpen.isLocallyClosed
  let q := pointOfClosedPoint fY y hyclosed
  have hrange : Set.range q ⊆ Set.range V.ι := by
    rintro _ ⟨z,rfl⟩
    have hqy : q z = y := pointOfClosedPoint_apply fY y hyclosed z
    exact ⟨⟨q z,hqy.symm ▸ hyV⟩,rfl⟩
  let qV := IsOpenImmersion.lift V.ι q hrange
  have hq : qV ≫ V.ι = q := IsOpenImmersion.lift_fac _ _ hrange
  have hsquare := IsPullback.of_right' (IsPullback.of_hasPullback g (qV ≫ V.ι))
    (isPullback_morphismRestrict g V).flip
  refine ⟨qV ≫ V.ι,?_,?_⟩
  · rw [hq]
    exact pointOfClosedPoint_comp fY y hyclosed
  · exact MorphismProperty.of_isPullback (P := @Etale) hsquare inferInstance

end M9Native.CurveEtaleRationalFibre
