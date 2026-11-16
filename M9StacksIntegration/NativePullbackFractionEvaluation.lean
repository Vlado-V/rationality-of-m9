module

public import M9StacksIntegration.NativeGenericPullbackEvaluation

@[expose] public section

/-! Actual numerator/denominator identities specialize on the genuine domain.

The rational pullback is an actual local-ring element whenever the image
point is generic.  Its universal numerator identity therefore specializes
even when the chosen denominator evaluates to zero.  This supplies the
constant-point cross identities from actual action pullbacks, rather than
assuming geometric invariance.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativePullbackFractionEvaluation

open NativeGenericPullbackEvaluation

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual global-section germ into the original function field. -/
def sectionToField (Y : Scheme.{u}) [IsIntegral Y] : Γ(Y, ⊤) →+* Y.functionField :=
  (Y.presheaf.germ ⊤ (genericPoint Y) (by trivial)).hom

/-- Evaluation of an original global section at the actual field-valued point. -/
def sectionValue {L : Type u} [Field L] (p : Spec (.of L) ⟶ Y) : Γ(Y, ⊤) →+* L :=
  (p.appTop ≫ (Scheme.ΓSpecIso (.of L)).hom).hom

omit [IsIntegral Y] in
/-- Actual global-section evaluation factors through the original stalk map. -/
theorem sectionValue_stalk {L : Type u} [Field L] (p : Spec (.of L) ⟶ Y)
    (c : Γ(Y, ⊤)) :
    Scheme.stalkClosedPointTo p
        (Y.presheaf.germ ⊤ (p (IsLocalRing.closedPoint L)) (by trivial) c) =
      sectionValue p c := by
  have he := Scheme.germ_stalkClosedPointTo (f := p) ⊤ (by trivial)
  have hv := congrArg (fun q : Γ(Y, ⊤) ⟶ CommRingCat.of L => q c) he
  simpa [sectionValue, Scheme.Hom.appTop] using hv

/-- The value of the genuine rational pullback at a point whose image is
generic, through the actual local ring at the parameter point. -/
def pointPullback {L : Type u} [Field L] (a : Y ⟶ X) (p : Spec (.of L) ⟶ Y)
    (ha : a (p (IsLocalRing.closedPoint L)) = genericPoint X) :
    X.functionField →+* L :=
  (stalkPullback a (p (IsLocalRing.closedPoint L)) ha ≫ Scheme.stalkClosedPointTo p).hom

omit [IsIntegral Y] in
/-- The local pullback is the original field embedding when the actual generic
scheme points agree. -/
theorem pointPullback_of_point {L : Type u} [Field L]
    (a : Y ⟶ X) (p : Spec (.of L) ⟶ Y) (s : X.functionField →+* L)
    (hs : p ≫ a = point s)
    (ha : a (p (IsLocalRing.closedPoint L)) = genericPoint X) :
    pointPullback a p ha = s :=
  congrArg CommRingCat.Hom.hom (point_stalkPullback a p s hs ha)

/-- A universal numerator identity specializes at every point where the
actual rational pullback is regular, including zero evaluations of the
chosen denominator. -/
theorem cross_identity_at_generic_image {L : Type u} [Field L]
    (a : Y ⟶ X) [IsDominant a] (p : Spec (.of L) ⟶ Y)
    (ha : a (p (IsLocalRing.closedPoint L)) = genericPoint X)
    (f : X.functionField) (n d : Γ(Y, ⊤))
    (h : NativeDominantFunctionField.map a f * sectionToField Y d = sectionToField Y n) :
    pointPullback a p ha f * sectionValue p d = sectionValue p n := by
  let y := p (IsLocalRing.closedPoint L)
  let : Nonempty (⊤ : Y.Opens) := ⟨⟨y, by trivial⟩⟩
  have hpull :
      algebraMap (Y.presheaf.stalk y) Y.functionField (stalkPullback a y ha f) =
        NativeDominantFunctionField.map a f := by
    change (stalkPullback a y ha ≫
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y))) f = _
    rw [stalkPullback_localize]
    rfl
  have hsection (c : Γ(Y, ⊤)) :
      algebraMap (Y.presheaf.stalk y) Y.functionField
        (Y.presheaf.germ ⊤ y (by trivial) c) = sectionToField Y c :=
    Y.algebraMap_germ_eq_germToFunctionField (by trivial) c
  have hlocal :
      stalkPullback a y ha f * Y.presheaf.germ ⊤ y (by trivial) d =
        Y.presheaf.germ ⊤ y (by trivial) n := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hpull, hsection, hsection]
    exact h
  have heval := congrArg
    (fun z : Y.presheaf.stalk y => (Scheme.stalkClosedPointTo p).hom z) hlocal
  rw [map_mul] at heval
  change pointPullback a p ha f *
      (Scheme.stalkClosedPointTo p).hom
        ((Y.presheaf.germ ⊤ (p (IsLocalRing.closedPoint L)) (by trivial)).hom d) =
    (Scheme.stalkClosedPointTo p).hom
      ((Y.presheaf.germ ⊤ (p (IsLocalRing.closedPoint L)) (by trivial)).hom n) at heval
  rw [sectionValue_stalk, sectionValue_stalk] at heval
  exact heval

/-- A genuine fraction representation supplies the cross identity without
any specialization-nonvanishing hypothesis on its chosen denominator. -/
theorem cross_identity_of_fraction_at_generic_image {L : Type u} [Field L]
    (a : Y ⟶ X) [IsDominant a] (p : Spec (.of L) ⟶ Y)
    (ha : a (p (IsLocalRing.closedPoint L)) = genericPoint X)
    (f : X.functionField) (n d : Γ(Y, ⊤))
    (hd : sectionToField Y d ≠ 0)
    (h : NativeDominantFunctionField.map a f = sectionToField Y n / sectionToField Y d) :
    pointPullback a p ha f * sectionValue p d = sectionValue p n := by
  apply cross_identity_at_generic_image a p ha f n d
  rw [h, div_mul_cancel₀ _ hd]

end M9Native.NativePullbackFractionEvaluation
