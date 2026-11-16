module

public import M9StacksIntegration.NativeFunctionFieldFunctor

@[expose] public section

/-! Evaluation of actual rational pullbacks on their genuine common domain.

The comparison passes through the actual local ring of the parameter point.
Its injection into the function field of the integral parameter scheme turns
equality of rational pullbacks into equality of local pullbacks.  Thus the
result applies even if a separately chosen numerator/denominator presentation
has a denominator vanishing at that parameter point.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace M9Native.NativeGenericPullbackEvaluation

open NativeFunctionFieldFunctor

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- The actual generic field point associated to a field embedding. -/
def point {L : Type u} [Field L] (s : X.functionField →+* L) : Spec (.of L) ⟶ X :=
  Spec.map (CommRingCat.ofHom s) ≫ genericSpec X

/-- Every point of the field spectrum maps to the actual generic point. -/
theorem point_apply {L : Type u} [Field L] (s : X.functionField →+* L)
    (z : Spec (.of L)) : point s z = genericPoint X := by
  change X.fromSpecStalk (genericPoint X) (Spec.map (CommRingCat.ofHom s) z) = _
  rw [Subsingleton.elim (Spec.map (CommRingCat.ofHom s) z)
    (IsLocalRing.closedPoint X.functionField)]
  exact Scheme.fromSpecStalk_closedPoint

/-- When the image is generic, the actual stalk map has the function field as
its source. This is the genuine regular pullback at the specified point. -/
def stalkPullback (a : Y ⟶ X) (y : Y) (hy : a y = genericPoint X) :
    X.functionField ⟶ Y.presheaf.stalk y :=
  (X.presheaf.stalkCongr (Inseparable.of_eq hy.symm)).hom ≫ a.stalkMap y

omit [IsIntegral Y] in
/-- The local pullback has the literal canonical scheme square. -/
theorem stalkPullback_square (a : Y ⟶ X) (y : Y) (hy : a y = genericPoint X) :
    Spec.map (stalkPullback a y hy) ≫ genericSpec X = Y.fromSpecStalk y ≫ a := by
  simp only [stalkPullback, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- Localizing the actual local pullback at the generic point gives the
original dominant function-field pullback. -/
theorem stalkPullback_localize (a : Y ⟶ X) [IsDominant a]
    (y : Y) (hy : a y = genericPoint X) :
    stalkPullback a y hy ≫
        Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y)) =
      CommRingCat.ofHom (NativeDominantFunctionField.map a) := by
  apply Spec.map_injective
  apply (cancel_mono (genericSpec X)).mp
  rw [Spec.map_comp, Category.assoc, stalkPullback_square, ← Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
  exact (map_square a).symm

/-- Equality of actual function-field pullbacks forces equality in the local
ring at any parameter point whose two images are generic. -/
theorem stalkPullback_eq_of_fieldPullback_eq (a b : Y ⟶ X)
    [IsDominant a] [IsDominant b] (y : Y)
    (ha : a y = genericPoint X) (hb : b y = genericPoint X) (f : X.functionField)
    (h : NativeDominantFunctionField.map a f = NativeDominantFunctionField.map b f) :
    stalkPullback a y ha f = stalkPullback b y hb f := by
  apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
  change
    (stalkPullback a y ha ≫
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y))) f =
    (stalkPullback b y hb ≫
      Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes (Set.mem_univ y))) f
  rw [stalkPullback_localize, stalkPullback_localize]
  exact h

omit [IsIntegral Y] in
/-- The actual parameter-point stalk pullback agrees with the original field
embedding whenever their actual generic scheme points agree. -/
theorem point_stalkPullback {L : Type u} [Field L]
    (a : Y ⟶ X) (p : Spec (.of L) ⟶ Y) (s : X.functionField →+* L)
    (hs : p ≫ a = point s)
    (ha : a (p (IsLocalRing.closedPoint L)) = genericPoint X) :
    stalkPullback a (p (IsLocalRing.closedPoint L)) ha ≫ Scheme.stalkClosedPointTo p =
      CommRingCat.ofHom s := by
  apply Spec.map_injective
  apply (cancel_mono (genericSpec X)).mp
  rw [Spec.map_comp, Category.assoc, stalkPullback_square, ← Category.assoc,
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact hs

/-- Equality of the actual rational pullbacks gives equality at arbitrary
field-valued parameter points on their genuine common domain. Only genericity
of the two images is used; no chosen denominator must survive specialization. -/
theorem eq_at_generic_points_of_pullbacks_eq {L : Type u} [Field L]
    (a b : Y ⟶ X) [IsDominant a] [IsDominant b]
    (p : Spec (.of L) ⟶ Y) (s t : X.functionField →+* L)
    (hs : p ≫ a = point s) (ht : p ≫ b = point t) (f : X.functionField)
    (h : NativeDominantFunctionField.map a f = NativeDominantFunctionField.map b f) :
    s f = t f := by
  let y := p (IsLocalRing.closedPoint L)
  have ha : a y = genericPoint X := by
    have he := congrArg (fun q : Spec (.of L) ⟶ X => q (IsLocalRing.closedPoint L)) hs
    exact he.trans (point_apply s _)
  have hb : b y = genericPoint X := by
    have he := congrArg (fun q : Spec (.of L) ⟶ X => q (IsLocalRing.closedPoint L)) ht
    exact he.trans (point_apply t _)
  have hlocal := stalkPullback_eq_of_fieldPullback_eq a b y ha hb f h
  have heval := congrArg (Scheme.stalkClosedPointTo p) hlocal
  change
    (stalkPullback a y ha ≫ Scheme.stalkClosedPointTo p) f =
    (stalkPullback b y hb ≫ Scheme.stalkClosedPointTo p) f at heval
  rw [point_stalkPullback a p s hs ha, point_stalkPullback b p t ht hb] at heval
  exact heval

end M9Native.NativeGenericPullbackEvaluation
