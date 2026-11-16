module

public import M9StacksIntegration.ProperSmoothLocus
public import StacksFrontier.AlgebraicGeometry.Properties.NoetherianClosedPoints

/-!
# Closed points detect the actual proper smooth-fibre locus

A point of an actual locally Noetherian fibre specializes to a closed
point of that fibre.  Over a closed base point, the closed fibre inclusion
sends it to a closed point of the original source.  Since the smooth locus
is open, checking those closed source points proves membership in the
original canonical good open.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace M9Native.ProperSmoothClosedPoints

/-- Every actual field-valued section has a closed image point. -/
theorem section_point_isClosed {K : Type u} [Field K] {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of K)) (p : Spec (.of K) ⟶ Y) (hp : p ≫ pY = 𝟙 _)
    (z : Spec (.of K)) : IsClosed ({p z} : Set Y) := by
  have : IsClosedImmersion p := isClosedImmersion_of_comp_eq_id pY p hp
  have hset : Set.range p = {p z} := by
    ext y
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg p (Subsingleton.elim a z)
    · rintro rfl
      exact ⟨z, rfl⟩
  exact hset ▸ p.isClosedEmbedding.isClosed_range

/-- The original fibre inclusion over a closed base point carries each
closed fibre point to an actual closed point of the original source. -/
theorem fiber_image_isClosed {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y)) (z : f.fiber y)
    (hz : IsClosed ({z} : Set (f.fiber y))) :
    IsClosed ({f.fiberι y z} : Set X) := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  have : IsClosedImmersion (f.fiberι y) :=
    inferInstanceAs (IsClosedImmersion (pullback.fst f (Y.fromSpecResidueField y)))
  simpa only [Set.image_singleton] using (f.fiberι y).isClosedMap {z} hz

/-- Actual smooth-locus membership on a fibre follows from checking the
closed source points of that same original fibre. -/
theorem smoothLocus_on_fiber_of_closed_points {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (y : Y) (hy : IsClosed ({y} : Set Y))
    (h : ∀ x : X, f x = y → IsClosed ({x} : Set X) → x ∈ f.smoothLocus)
    (z : f.fiber y) : f.fiberι y z ∈ f.smoothLocus := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y)))
  let : IsLocallyNoetherian (f.fiber y) :=
    LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  obtain ⟨w, hw, hzw⟩ := exists_specializes_closedPoint (f.fiber y) z
  have hfw : f (f.fiberι y w) = y := by
    have hm : f.fiberι y w ∈ f ⁻¹' {y} := (f.range_fiberι y).le ⟨w, rfl⟩
    exact hm
  have hsm := h (f.fiberι y w) hfw (fiber_image_isClosed f y hy w hw)
  exact (hzw.map (f.fiberι y).continuous).mem_open f.smoothLocus.isOpen hsm

/-- Checking actual relative smoothness at closed points is enough to
put the whole original fibre in the canonical actual good open. -/
theorem mem_goodOpen_of_closed_points {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] [IsProper f] (y : Y)
    (hy : IsClosed ({y} : Set Y))
    (h : ∀ x : X, f x = y → IsClosed ({x} : Set X) → x ∈ f.smoothLocus) :
    y ∈ ProperSmoothLocus.goodOpen f := by
  apply (ProperSmoothLocus.mem_goodOpen_iff f y).mpr
  intro x hfx
  have hrange : x ∈ Set.range (f.fiberι y) := by
    rw [f.range_fiberι y]
    exact hfx
  obtain ⟨z, rfl⟩ := hrange
  exact smoothLocus_on_fiber_of_closed_points f y hy h z

end M9Native.ProperSmoothClosedPoints
