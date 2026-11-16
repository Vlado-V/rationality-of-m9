module

public import M9StacksIntegration.CanonicalDivisorSpan
public import M9StacksIntegration.FiniteCurveDivisor
public import StacksFrontier.AlgebraicGeometry.Curves.NodalCurveComponents

/-!
# The actual reduced divisor of finitely many distinct rational points

A tuple of closed points constructs its reduced closed subscheme. Its
finite scheme length is the tuple cardinality, and on an original smooth
proper curve with no degree-three pencil the canonical evaluation on
any actual three distinct points has rank three. No divisor, length,
Cartier structure, or evaluation-rank premise is supplied.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace M9Native.RationalPointDivisor

variable {X : Scheme.{u}} {n : ℕ} (c : Fin n → closedPoints X)

/-- The finite closed subset in the original curve. -/
def pointSet : Closeds X :=
  ⟨Set.range (fun i => (c i).1), by
    simpa only [Set.iUnion_singleton_eq_range] using
      isClosed_iUnion_of_finite (fun i : Fin n => (c i).2)⟩

/-- The literal reduced closed subscheme on those original points. -/
def divisor : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal (pointSet c)

instance divisor_reduced : IsReduced (divisor c).subscheme :=
  Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (pointSet c)

/-- The underlying space is the actual finite point subset. -/
def subschemeHomeo : (divisor c).subscheme ≃ₜ Set.range (fun i => (c i).1) :=
  (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso (divisor c).subschemeIso)).trans
      (divisor c).gluedHomeo |>.trans
    (Homeomorph.setCongr (Scheme.IdealSheafData.coe_support_vanishingIdeal (pointSet c)))

/-- Distinct labels enumerate the actual subscheme points. -/
def subschemeEquivFin (hc : Function.Injective c) : (divisor c).subscheme ≃ Fin n :=
  (subschemeHomeo c).toEquiv.trans
    (Equiv.ofInjective (fun i => (c i).1) (fun _ _ h => hc (Subtype.ext h))).symm

instance divisor_finite : Finite (divisor c).subscheme := by
  let : Finite (Set.range (fun i => (c i).1)) := (Set.finite_range _).to_subtype
  exact Finite.of_equiv _ (subschemeHomeo c).toEquiv.symm

instance divisor_t1 : T1Space (divisor c).subscheme := by
  refine ⟨fun x => ?_⟩
  apply (divisor c).subschemeι.isClosedEmbedding.isClosed_iff_image_isClosed.mpr
  rw [Set.image_singleton]
  have hr : Set.range (divisor c).subschemeι = Set.range (fun i => (c i).1) :=
    (divisor c).range_subschemeι.trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal (pointSet c))
  obtain ⟨i,hi⟩ := hr ▸ (show (divisor c).subschemeι x ∈
      Set.range (divisor c).subschemeι from ⟨x,rfl⟩)
  exact hi ▸ (c i).2

/-- The actual finite closed subscheme is zero dimensional. -/
theorem dimension_le_zero : topologicalKrullDim (divisor c).subscheme ≤ 0 :=
  topologicalKrullDim_zero_of_discreteTopology _

variable {K : Type u} [Field K] [IsAlgClosed K]
    (f : X ⟶ Spec (.of K)) [IsProper f]

omit [IsAlgClosed K] in
/-- Properness and the proved zero dimension derive finiteness. -/
theorem divisor_isFinite : IsFinite ((divisor c).subschemeι ≫ f) :=
  isFinite_of_isProper_of_topologicalKrullDim_le_zero _ (dimension_le_zero c)

/-- Reducedness is derived and counts the actual length, using the
original structural field action on global sections. -/
theorem length_eq (hc : Function.Injective c) :
    letI : Algebra K Γ((divisor c).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((divisor c).subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank K Γ((divisor c).subscheme, ⊤) = n := by
  let := divisor_isFinite c f
  exact (finrank_globalSections_eq_natCard_of_isReduced K
    ((divisor c).subschemeι ≫ f)).trans (Nat.card_eq_of_equiv_fin (subschemeEquivFin c hc))

variable [IsCurve K f] [Smooth f]

include f in
omit [IsAlgClosed K] [IsProper f] in
/-- The actual tuple divisor is Cartier on the original smooth curve. -/
theorem divisor_cartier : Stacks.Divisors.IsEffectiveCartierDivisor (divisor c) :=
  FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f (divisor c)
    (dimension_le_zero c)

variable [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)]

/-- Actual Riemann--Roch and the no-degree-three theorem force every
actual distinct triple of original points to have canonical rank three. -/
theorem canonical_rank_three (c : Fin 3 → closedPoints X) (hc : Function.Injective c)
    (hdim : topologicalKrullDim X ≤ 1)
    (hno3 : ¬ Nonempty (LinearSeries K f hdim 3 1)) :
    Module.finrank K (LinearMap.range
      (CanonicalDivisorSpan.canonicalRestriction f (divisor c))) = 3 := by
  let := divisor_cartier c f
  have hOD := M9StacksIntegration.CanonicalPencilBounds.divisor_h0_eq_one_of_no_pencil
    f hdim 3 hno3 (divisor c) (length_eq c f hc)
  have hRR := CanonicalDivisorSpan.restriction_rank_add_divisor_h0 f (divisor c)
  rw [length_eq c f hc] at hRR
  change _ + Module.finrank K (cohomologyOverField K f
    (Stacks.Divisors.invertibleSheaf' (divisor c)) 0) = 3 + 1 at hRR
  rw [hOD] at hRR
  omega

end M9Native.RationalPointDivisor
