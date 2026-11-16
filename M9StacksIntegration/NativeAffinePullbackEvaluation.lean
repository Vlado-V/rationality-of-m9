module

public import M9StacksIntegration.NativePullbackFractionEvaluation

@[expose] public section

/-! Literal affine-coordinate specialization of actual rational pullbacks.
The formulas use the actual affine generic stalk and actual field-valued
scheme point, including points where a chosen denominator evaluates to zero.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativeAffinePullbackEvaluation

open NativePullbackFractionEvaluation NativeGenericPullbackEvaluation

/-- The actual affine section germ is the original fraction-ring inclusion. -/
theorem sectionToField_affine (R : Type u) [CommRing R] [IsDomain R] (r : R) :
    sectionToField (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv r) =
      algebraMap R (Spec (.of R)).functionField r := rfl

/-- Actual affine-point evaluation is the original coordinate-ring map. -/
theorem sectionValue_specMap {R L : Type u} [CommRing R] [Field L]
    (κ : R →+* L) (r : R) :
    sectionValue (Spec.map (CommRingCat.ofHom κ)) ((Scheme.ΓSpecIso (.of R)).inv r) =
      κ r := by
  change ((Scheme.ΓSpecIso (.of R)).inv ≫ (Spec.map (CommRingCat.ofHom κ)).appTop ≫
    (Scheme.ΓSpecIso (.of L)).hom) r = _
  rw [← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

/-- A universal actual numerator identity specializes at every affine field
point whose image in the original variety is generic. -/
theorem cross_identity_at_affine_point {X : Scheme.{u}} [IsIntegral X]
    (R : Type u) [CommRing R] [IsDomain R] {L : Type u} [Field L]
    (a : Spec (.of R) ⟶ X) [IsDominant a] (κ : R →+* L)
    (ha : a (Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint L)) = genericPoint X)
    (f : X.functionField) (n d : R)
    (h : NativeDominantFunctionField.map a f *
      algebraMap R (Spec (.of R)).functionField d =
      algebraMap R (Spec (.of R)).functionField n) :
    pointPullback a (Spec.map (CommRingCat.ofHom κ)) ha f * κ d = κ n := by
  have h' : NativeDominantFunctionField.map a f *
      sectionToField (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv d) =
      sectionToField (Spec (.of R)) ((Scheme.ΓSpecIso (.of R)).inv n) :=
    (congrArg (fun q => NativeDominantFunctionField.map a f * q)
      (sectionToField_affine R d)).trans (h.trans (sectionToField_affine R n).symm)
  have hc := cross_identity_at_generic_image a (Spec.map (CommRingCat.ofHom κ)) ha f
    ((Scheme.ΓSpecIso (.of R)).inv n) ((Scheme.ΓSpecIso (.of R)).inv d) h'
  exact (congrArg (fun q => pointPullback a (Spec.map (CommRingCat.ofHom κ)) ha f * q)
    (sectionValue_specMap κ d).symm).trans (hc.trans (sectionValue_specMap κ n))

/-- The actual fraction representation suffices; the chosen denominator is
not required to have nonzero value at the affine field point. -/
theorem cross_identity_of_fraction_at_affine_point {X : Scheme.{u}} [IsIntegral X]
    (R : Type u) [CommRing R] [IsDomain R] {L : Type u} [Field L]
    (a : Spec (.of R) ⟶ X) [IsDominant a] (κ : R →+* L)
    (ha : a (Spec.map (CommRingCat.ofHom κ) (IsLocalRing.closedPoint L)) = genericPoint X)
    (f : X.functionField) (n d : R) (hd : d ≠ 0)
    (h : NativeDominantFunctionField.map a f =
      algebraMap R (Spec (.of R)).functionField n /
        algebraMap R (Spec (.of R)).functionField d) :
    pointPullback a (Spec.map (CommRingCat.ofHom κ)) ha f * κ d = κ n := by
  apply cross_identity_at_affine_point R a κ ha f n d
  rw [h]
  apply div_mul_cancel₀
  intro hz
  exact hd (IsFractionRing.injective R (Spec (.of R)).functionField (by simpa using hz))

end M9Native.NativeAffinePullbackEvaluation
