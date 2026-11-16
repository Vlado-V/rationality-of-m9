module

public import M9StacksIntegration.Sp6AffinePoints

@[expose] public section

/-! The actual affine-coordinate homomorphism of an arbitrary extension-valued
native group point, with its structural coefficient compatibility derived.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.Sp6AffineExtensionPoints

variable (K R : Type u) [CommRing K] [CommRing R] [Algebra K R]

abbrev source : Over (Spec (.of K)) := Over.mk (Sp6AffineBaseChange.specAlgebraMap K R)

def coordinateHom (g : source K R ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    Sp6AffinePoints.CoordinateRing K →+* R :=
  (Spec.preimage ((g ≫ (Sp6AffineBaseChange.overIso K).inv).left)).hom

/-- The actual over-scheme square forces preservation of the coefficient field. -/
theorem coordinateHom_commutes (g : source K R ⟶ Sp6GroupScheme.obj (Spec (.of K)))
    (c : K) : coordinateHom K R g (algebraMap K (Sp6AffinePoints.CoordinateRing K) c) =
      algebraMap K R c := by
  let q := g ≫ (Sp6AffineBaseChange.overIso K).inv
  have he : CommRingCat.ofHom (algebraMap K (Sp6AffinePoints.CoordinateRing K)) ≫
      Spec.preimage q.left = CommRingCat.ofHom (algebraMap K R) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage]
    exact q.w
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of R => f c) he

def algebraOfPoint (g : source K R ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    Sp6AffinePoints.CoordinateRing K →ₐ[K] R where
  __ := coordinateHom K R g
  commutes' c := coordinateHom_commutes K R g c

/-- Recovering affine coordinates and then the actual native point is identity. -/
theorem point_algebraOfPoint (g : source K R ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    Sp6AffinePoints.point K (algebraOfPoint K R g) = g := by
  apply (cancel_mono (Sp6AffineBaseChange.overIso K).inv).mp
  rw [Sp6AffinePoints.point, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Over.OverMorphism.ext
  exact Spec.map_preimage _

theorem algebraOfPoint_point (χ : Sp6AffinePoints.CoordinateRing K →ₐ[K] R) :
    algebraOfPoint K R (Sp6AffinePoints.point K χ) = χ := by
  ext r
  change (Spec.preimage
    ((Sp6AffinePoints.point K χ ≫ (Sp6AffineBaseChange.overIso K).inv).left)) r = χ r
  have he : (Sp6AffinePoints.point K χ ≫ (Sp6AffineBaseChange.overIso K).inv).left =
      Spec.map (CommRingCat.ofHom χ.toRingHom) := by
    simp only [Sp6AffinePoints.point, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [he, Spec.preimage_map]
  rfl

def pointEquiv : (Sp6AffinePoints.CoordinateRing K →ₐ[K] R) ≃
    (source K R ⟶ Sp6GroupScheme.obj (Spec (.of K))) where
  toFun := Sp6AffinePoints.point K
  invFun := algebraOfPoint K R
  left_inv := algebraOfPoint_point K R
  right_inv := point_algebraOfPoint K R

end M9Native.Sp6AffineExtensionPoints
