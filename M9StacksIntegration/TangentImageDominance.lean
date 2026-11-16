module

public import M9StacksIntegration.DominantSmoothClosedPoint
public import M9StacksIntegration.SmoothTangentMapSurjective
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointResidueField

/-!
# Genuine dominance obstruction from canonical tangent-image rank

At a closed point over an algebraically closed field the actual canonical
residue-field map is an isomorphism. The image below is the literal image
of the original native tangent map, over the original image residue field.
Dominance in characteristic zero forces that image to have the full
smooth target dimension somewhere. Thus an everywhere smaller image
forces a genuine dense open avoiding the actual morphism's image.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace M9Native.TangentImageDominance
universe u
variable (K : Type u) [Field K] [IsAlgClosed K]
  {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of K)) [LocallyOfFiniteType sX]
  (sY : Y ⟶ Spec (.of K)) (f : X ⟶ Y) (hf : f ≫ sY = sX)

include hf in
/-- The canonical residue-field map is genuinely an isomorphism at every
actual closed source point over the original algebraically closed field. -/
theorem residueFieldMap_isIso (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIso (f.residueFieldMap x) := by
  have : LocallyOfFiniteType (f ≫ sY) := by rw [hf]; infer_instance
  exact isIso_residueFieldMap_of_isClosed f sY x hx

/-- The literal image of the actual original native tangent map at a
closed point. Its scalar field is the actual residue field of the image. -/
def tangentImageAtClosed (x : X) (hx : IsClosed ({x} : Set X)) :
    Submodule (Y.residueField (f x)) (DottedTangentArrow sY (f x)) := by
  have : IsIso (f.residueFieldMap x) := residueFieldMap_isIso K sX sY f hf x hx
  have : RingHomSurjective (inv (f.residueFieldMap x)).hom :=
    ⟨(ConcreteCategory.bijective_of_isIso (inv (f.residueFieldMap x))).surjective⟩
  exact (tangentMap f sX sY hf x).range

/-- At a genuinely formally smooth original stalk, the actual canonical
tangent image is the whole actual target tangent space. -/
theorem tangentImageAtClosed_eq_top (x : X) (hx : IsClosed ({x} : Set X))
    (hsm : (f.stalkMap x).hom.FormallySmooth) :
    tangentImageAtClosed K sX sY f hf x hx = ⊤ := by
  have : IsIso (f.residueFieldMap x) := residueFieldMap_isIso K sX sY f hf x hx
  have : RingHomSurjective (inv (f.residueFieldMap x)).hom :=
    ⟨(ConcreteCategory.bijective_of_isIso (inv (f.residueFieldMap x))).surjective⟩
  change (tangentMap f sX sY hf x).range = ⊤
  exact LinearMap.range_eq_top.mpr
    (SmoothTangentMapSurjective.tangentMap_surjective f sX sY hf x hsm)

/-- Full rank is computed from the actual target smooth relative
dimension, without any bound or dimension input on the source. -/
theorem tangentImageAtClosed_finrank_of_formallySmooth
    (n : ℕ) [SmoothOfRelativeDimension n sY]
    (x : X) (hx : IsClosed ({x} : Set X)) (hsm : (f.stalkMap x).hom.FormallySmooth) :
    Module.finrank (Y.residueField (f x)) (tangentImageAtClosed K sX sY f hf x hx) = n := by
  rw [tangentImageAtClosed_eq_top K sX sY f hf x hx hsm, finrank_top]
  exact Scheme.Hom.finrank_dottedTangentArrow_of_smoothOfRelativeDimension sY n (f x)

/-- A dominant actual map of integral characteristic-zero varieties to a
smooth target has full canonical tangent-image rank at an actual closed
rational source point. -/
theorem exists_full_rank_closed_rational_point [CharZero K] [IsIntegral X] [IsIntegral Y]
    (n : ℕ) [SmoothOfRelativeDimension n sY] [LocallyOfFiniteType f] [IsDominant f] :
    ∃ (x : X) (σ : Spec (.of K) ⟶ X) (hx : IsClosed ({x} : Set X)),
      σ ≫ sX = 𝟙 _ ∧ σ (IsLocalRing.closedPoint K) = x ∧
      Module.finrank (Y.residueField (f x)) (tangentImageAtClosed K sX sY f hf x hx) = n := by
  have : Smooth sY := SmoothOfRelativeDimension.smooth n sY
  obtain ⟨x, σ, hx, hsm, hσ, hσx⟩ :=
    DominantSmoothClosedPoint.exists_closed_rational_smooth_point K sX sY f
  exact ⟨x, σ, hx, hσ, hσx,
    tangentImageAtClosed_finrank_of_formallySmooth K sX sY f hf n x hx hsm⟩

/-- Uniformly smaller actual canonical tangent images force genuine
nondominance. No source-count or nondominance hypothesis is supplied. -/
theorem not_isDominant_of_tangentImage_rank_le [CharZero K] [IsIntegral X] [IsIntegral Y]
    (n m : ℕ) [SmoothOfRelativeDimension n sY] [LocallyOfFiniteType f]
    (hmn : m < n)
    (hbound : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      Module.finrank (Y.residueField (f x)) (tangentImageAtClosed K sX sY f hf x hx) ≤ m) :
    ¬ IsDominant f := by
  intro hd
  have : IsDominant f := hd
  obtain ⟨x, _, hx, _, _, hrank⟩ :=
    exists_full_rank_closed_rational_point K sX sY f hf n
  have hle := hbound x hx
  rw [hrank] at hle
  exact (Nat.not_le_of_lt hmn) hle

/-- The literal image of a genuinely nondominant morphism misses an
actual nonempty dense open of an integral target. -/
theorem exists_dense_open_avoiding_image_of_not_isDominant [IsIntegral Y]
    (hd : ¬ IsDominant f) :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ Dense (U : Set Y) ∧ ∀ x : X, f x ∉ U := by
  let U : Y.Opens := ⟨(closure (Set.range f))ᶜ, isClosed_closure.isOpen_compl⟩
  have hU : (U : Set Y).Nonempty := by
    by_contra he
    apply hd
    constructor
    intro y
    by_contra hy
    exact he ⟨y, hy⟩
  exact ⟨U, hU, U.isOpen.dense hU, fun x hx => hx (subset_closure ⟨x, rfl⟩)⟩

/-- A uniform actual tangent-image rank bound smaller than the smooth
target dimension gives an actual dense open avoiding the actual image. -/
theorem exists_dense_open_avoiding_tangentImage_rank_le
    [CharZero K] [IsIntegral X] [IsIntegral Y]
    (n m : ℕ) [SmoothOfRelativeDimension n sY] [LocallyOfFiniteType f]
    (hmn : m < n)
    (hbound : ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      Module.finrank (Y.residueField (f x)) (tangentImageAtClosed K sX sY f hf x hx) ≤ m) :
    ∃ U : Y.Opens, (U : Set Y).Nonempty ∧ Dense (U : Set Y) ∧ ∀ x : X, f x ∉ U :=
  exists_dense_open_avoiding_image_of_not_isDominant f
    (not_isDominant_of_tangentImage_rank_le K sX sY f hf n m hmn hbound)

end M9Native.TangentImageDominance
