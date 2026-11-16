module

public import M9StacksIntegration.ExpectedFiberFlatness
public import StacksFrontier.AlgebraicGeometry.Properties.RegularCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.Regular
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Actual closed-point adapters for the expected-fibre flatness bridge

Regular stalks come from actual smoothness over the field.  Dimensions of
closed stalks come from actual local dimensions, and the fibre stalk is
retained literally.  The last result derives flatness of the original
stalk map; flatness or relative smoothness is never an input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ExpectedFiberClosedPoints

/-- Regularity of the original scheme gives regularity of each actual stalk. -/
theorem regular_stalk_of_regular {X : Scheme.{u}} (hX : IsRegular X) (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  (((isRegular_tfae X).out 1 2 rfl rfl).mp hX).2 x

/-- An actual smooth scheme over a field has regular actual local rings. -/
theorem regular_stalk_of_smooth {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [Smooth p] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) :=
  regular_stalk_of_regular (isRegular_of_smooth_over_field p) x

/-- For an irreducible scheme of finite type over a field, the actual
closed stalk has the actual global dimension. -/
theorem closed_stalk_dimension {K : Type u} [Field K] {X : Scheme.{u}}
    (p : X ⟶ Spec (.of K)) [LocallyOfFiniteType p] [IrreducibleSpace X]
    (x : X) (hx : IsClosed ({x} : Set X)) {d : ℕ}
    (hdim : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    ringKrullDim (X.presheaf.stalk x) = (d : WithBot ℕ∞) :=
  (topologicalKrullDimAt_eq_krullDimOfRing_stalk K X p x hx).symm.trans
    ((topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible K X p x).symm.trans hdim)

/-- A closed point over a closed base point remains closed in its actual
scheme-theoretic fibre. -/
theorem asFiber_isClosed {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y)) :
    IsClosed ({f.asFiber x} : Set (f.fiber (f x))) := by
  let : IsClosedImmersion (Y.fromSpecResidueField (f x)) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsClosedImmersion (f.fiberι (f x)) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Y.fromSpecResidueField (f x))))
  have hset : (f.fiberι (f x)) ⁻¹' ({x} : Set X) = {f.asFiber x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro hz
      apply (f.fiberι (f x)).isClosedEmbedding.injective
      exact hz.trans (f.fiberι_asFiber x).symm
    · rintro rfl
      exact f.fiberι_asFiber x
  exact hset ▸ hx.preimage (f.fiberι (f x)).continuous

/-- The closed stalk of an actual irreducible fibre has the proved
dimension of that original fibre. -/
theorem fiber_stalk_dimension {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X))
    (hy : IsClosed ({f x} : Set Y)) [IrreducibleSpace (f.fiber (f x))] {d : ℕ}
    (hdim : topologicalKrullDim (f.fiber (f x)) = (d : WithBot ℕ∞)) :
    ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) = (d : WithBot ℕ∞) := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField (f x))))
  exact closed_stalk_dimension (f.fiberToSpecResidueField (f x)) (f.asFiber x)
    (asFiber_isClosed f x hx hy) hdim

/-- Actual absolute smoothness, actual closed-point dimensions and the
actual expected fibre dimension derive flatness of the original map at
that closed point. -/
theorem flat_stalkMap_of_closed_dimensions {K : Type u} [Field K]
    {X Y : Scheme.{u}} (pX : X ⟶ Spec (.of K)) (pY : Y ⟶ Spec (.of K))
    [Smooth pX] [Smooth pY] (f : X ⟶ Y) [LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({f x} : Set Y))
    [IrreducibleSpace (f.fiber (f x))] {n m r : ℕ}
    (hX : topologicalKrullDimAt X x = (n : WithBot ℕ∞))
    (hY : topologicalKrullDimAt Y (f x) = (m : WithBot ℕ∞))
    (hF : topologicalKrullDim (f.fiber (f x)) = (r : WithBot ℕ∞)) (hn : n = m + r) :
    (f.stalkMap x).hom.Flat := by
  let : IsRegularLocalRing (X.presheaf.stalk x) := regular_stalk_of_smooth pX x
  let : IsRegularLocalRing (Y.presheaf.stalk (f x)) := regular_stalk_of_smooth pY (f x)
  have hS : ringKrullDim (X.presheaf.stalk x) = (n : WithBot ℕ∞) :=
    (topologicalKrullDimAt_eq_krullDimOfRing_stalk K X pX x hx).symm.trans hX
  have hR : ringKrullDim (Y.presheaf.stalk (f x)) = (m : WithBot ℕ∞) :=
    (topologicalKrullDimAt_eq_krullDimOfRing_stalk K Y pY (f x) hy).symm.trans hY
  have hFib := fiber_stalk_dimension f x hx hy hF
  apply ExpectedFiberFlatness.flat_stalkMap_of_dimension_eq f x
  rw [hS, hR, hFib]
  exact_mod_cast hn

end M9Native.ExpectedFiberClosedPoints
