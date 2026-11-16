module

public import M9StacksIntegration.PencilProjectiveLineGeometry
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Basic

/-!
# The actual field fibre of the original constant projective-line family

The isomorphism is constructed from the two genuine pullback squares and
native projective-space base change. It preserves the original structure
map and the original morphism to the initial projective line.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.ConstantProjectiveLineFibre

open PencilProjectiveLineGeometry

variable (K L : Type u) [Field K] [Field L] {T : Scheme.{u}}
  (s : T ⟶ Spec (.of K)) (i : Spec (.of L) ⟶ T)

/-- The original constant target family, not an assumed projective-line model. -/
def target : Scheme.{u} := pullback (toBase K) s

/-- Its actual projection. -/
def projection : target K s ⟶ T := pullback.snd (toBase K) s

/-- The original scheme-theoretic fibre over the specified actual field point. -/
def fieldFibre : Scheme.{u} := pullback (projection K s) i

/-- The pasted original square is an actual pullback over the original field base. -/
theorem fieldFibre_isPullback :
    IsPullback
      (pullback.fst (projection K s) i ≫ pullback.fst (toBase K) s)
      (pullback.snd (projection K s) i) (toBase K) (i ≫ s) :=
  (IsPullback.of_hasPullback (projection K s) i).paste_horiz
    (IsPullback.of_hasPullback (toBase K) s)

/-- The actual fibre is canonically the literal native projective line over `L`. -/
def fibreIso : fieldFibre K L s i ≅ Line L :=
  (fieldFibre_isPullback K L s i).isoIsPullback _ _
    (isPullback_projectiveSpaceOverMap 1 (i ≫ s))

/-- The comparison retains the actual field-fibre structural map. -/
theorem fibreIso_over :
    (fibreIso K L s i).hom ≫ toBase L = pullback.snd (projection K s) i :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The comparison retains the actual projection to the original projective line. -/
theorem fibreIso_toOriginal :
    (fibreIso K L s i).hom ≫ projectiveSpaceOverMap 1 (i ≫ s) =
      pullback.fst (projection K s) i ≫ pullback.fst (toBase K) s :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

end M9Native.ConstantProjectiveLineFibre
