module

public import M9StacksIntegration.Sp6AffineBaseChange
public import M9StacksIntegration.PrimitiveRingFieldBridge

@[expose] public section

/-! Actual algebra points of the original affine Sp6 presentation.
The equivalence uses the checked native scheme isomorphism and Spec's actual
fully faithful inverse. Constant matrices are decoded through the original
native group-point equivalence, including the actual identity evaluation.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace M9Native.Sp6AffinePoints

abbrev CoordinateRing (K : Type u) [CommRing K] := Sp6AffineBaseChange.CoordinateRing K

variable (K : Type u) [CommRing K]

/-- An actual algebra homomorphism gives its actual group-scheme point. -/
def point {R : Type u} [CommRing R] [Algebra K R]
    (χ : CoordinateRing K →ₐ[K] R) :
    Over.mk (Sp6AffineBaseChange.specAlgebraMap K R) ⟶
      Sp6GroupScheme.obj (Spec (.of K)) :=
  (Over.homMk (Spec.map (CommRingCat.ofHom χ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
      Sp6AffineBaseChange.projection K = Sp6AffineBaseChange.specAlgebraMap K R
    dsimp only [Sp6AffineBaseChange.projection, Sp6AffineBaseChange.specAlgebraMap]
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact χ.commutes c) :
    Over.mk (Sp6AffineBaseChange.specAlgebraMap K R) ⟶
      Over.mk (Sp6AffineBaseChange.projection K)) ≫ (Sp6AffineBaseChange.overIso K).hom

/-- Base-field points use the literal identity base object. -/
def basePoint (χ : CoordinateRing K →ₐ[K] K) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K)) :=
  (Over.homMk (Spec.map (CommRingCat.ofHom χ.toRingHom)) (by
    change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫
      Sp6AffineBaseChange.projection K = 𝟙 _
    dsimp only [Sp6AffineBaseChange.projection, Sp6AffineBaseChange.specAlgebraMap]
    rw [← Spec.map_comp]
    have he : CommRingCat.ofHom (algebraMap K (CoordinateRing K)) ≫
        CommRingCat.ofHom χ.toRingHom = 𝟙 (CommRingCat.of K) := by
      ext c
      exact χ.commutes c
    rw [he, Spec.map_id]) :
    Over.mk (𝟙 (Spec (.of K))) ⟶ Over.mk (Sp6AffineBaseChange.projection K)) ≫
      (Sp6AffineBaseChange.overIso K).hom

/-- The original affine-coordinate map of an actual base-field group point. -/
def ringOfBasePoint
    (g : Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    CoordinateRing K →+* K :=
  (Spec.preimage ((g ≫ (Sp6AffineBaseChange.overIso K).inv).left)).hom

theorem ringOfBasePoint_commutes
    (g : Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K))) (c : K) :
    ringOfBasePoint K g (algebraMap K (CoordinateRing K) c) = c := by
  let q := g ≫ (Sp6AffineBaseChange.overIso K).inv
  have he : CommRingCat.ofHom (algebraMap K (CoordinateRing K)) ≫
      Spec.preimage q.left = 𝟙 (CommRingCat.of K) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact q.w
  exact congrArg (fun f : CommRingCat.of K ⟶ CommRingCat.of K => f c) he

def algebraOfBasePoint
    (g : Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    CoordinateRing K →ₐ[K] K where
  __ := ringOfBasePoint K g
  commutes' c := ringOfBasePoint_commutes K g c

theorem basePoint_algebraOfBasePoint
    (g : Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K))) :
    basePoint K (algebraOfBasePoint K g) = g := by
  apply (cancel_mono (Sp6AffineBaseChange.overIso K).inv).mp
  rw [basePoint, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply Over.OverMorphism.ext
  exact Spec.map_preimage _

theorem algebraOfBasePoint_basePoint (χ : CoordinateRing K →ₐ[K] K) :
    algebraOfBasePoint K (basePoint K χ) = χ := by
  ext r
  change (Spec.preimage ((basePoint K χ ≫ (Sp6AffineBaseChange.overIso K).inv).left)) r = χ r
  have he : (basePoint K χ ≫ (Sp6AffineBaseChange.overIso K).inv).left =
      Spec.map (CommRingCat.ofHom χ.toRingHom) := by
    simp only [basePoint, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rfl
  rw [he, Spec.preimage_map]
  rfl

/-- Actual algebra points and actual native group points are equivalent. -/
def basePointEquiv : (CoordinateRing K →ₐ[K] K) ≃
    (Over.mk (𝟙 (Spec (.of K))) ⟶ Sp6GroupScheme.obj (Spec (.of K))) where
  toFun := basePoint K
  invFun := algebraOfBasePoint K
  left_inv := algebraOfBasePoint_basePoint K
  right_inv := basePoint_algebraOfBasePoint K

/-- The actual coordinate-ring evaluation at the original group identity. -/
def identityEvaluation : CoordinateRing K →ₐ[K] K := (basePointEquiv K).symm 1

@[simp]
theorem basePoint_identityEvaluation : basePoint K (identityEvaluation K) = 1 :=
  (basePointEquiv K).apply_symm_apply 1

/-- The original constant symplectic matrix represented by an algebra point. -/
def matrixPoint (χ : CoordinateRing K →ₐ[K] K) : Matrix.symplecticGroup (Fin 3) K :=
  Sp6GroupScheme.mapMatrix (Scheme.ΓSpecIso (.of K)).hom.hom
    (Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) (Over.mk (𝟙 _)) (basePoint K χ))

/-- Its native constant group point is exactly the original algebra point. -/
theorem constantPoint_matrixPoint (χ : CoordinateRing K →ₐ[K] K) :
    Sp6GroupScheme.constantPoint K (matrixPoint K χ) = basePoint K χ := by
  apply (Sp6GroupScheme.pointsMulEquiv (Spec (.of K)) (Over.mk (𝟙 _))).injective
  rw [Sp6GroupScheme.pointsMulEquiv_constantPoint]
  apply Subtype.ext
  ext i j
  exact Iso.hom_inv_id_apply (Scheme.ΓSpecIso (.of K)) _

/-- The literal original Sp6(C) element, through the frozen split-basis bridge. -/
def originalElement (χ : CoordinateRing ℂ →ₐ[ℂ] ℂ) : M9.PrimitiveStabilizer.Sp6 ℂ :=
  PrimitiveRingFieldBridge.toOriginal (matrixPoint ℂ χ)

theorem constantPoint_originalElement (χ : CoordinateRing ℂ →ₐ[ℂ] ℂ) :
    Sp6GroupScheme.constantPoint ℂ (PrimitiveRingFieldBridge.fromOriginal (originalElement χ)) =
      basePoint ℂ χ := by
  rw [originalElement, PrimitiveRingFieldBridge.fromOriginal_toOriginal]
  exact constantPoint_matrixPoint ℂ χ

end M9Native.Sp6AffinePoints
