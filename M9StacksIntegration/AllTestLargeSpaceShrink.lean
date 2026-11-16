module

public import M9StacksIntegration.AllTestLargeSpaceSmallSections
public import Mathlib.CategoryTheory.EssentialImage

/-!
# Actual same-presheaf universe descent from an original atlas

Pointwise smallness is proved by AllTestLargeSpaceSmallSections from the
actual original representable locally surjective atlas. The essential-image
lift along the fully faithful universe lift constructs the small presheaf,
with a genuine natural isomorphism on EVERY original test and map. The
actual sheaf condition is reflected through that isomorphism; no original
Type-u sheafification or classification hypothesis is used.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestLargeSpaceShrink
open AllTestLargeSpaceSmallSections AllTestSheafCoproducts AllTestCoproductCartesian
universe u

/-- A genuinely small large-universe type is in the actual universe lift's
essential image, by its chosen Shrink equivalence. -/
theorem essImage_ulift_of_small (X : Type (u+1)) [Small.{u} X] :
    uliftFunctor.{u+1, u}.essImage X :=
  ⟨Shrink.{u} X, ⟨(Equiv.ulift.trans (equivShrink X).symm).toIso⟩⟩

variable (K : Type u) [Field K]

/-- The actual pointwise small model as a functor on the unchanged full site. -/
def smallPresheaf (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (h : ∀ T, Small.{u} (F.obj T)) : M9StandaloneDraft.Presheaves K :=
  Functor.essImage.liftFunctor F uliftFunctor.{u+1, u} (fun T => by
    let : Small.{u} (F.obj T) := h T
    exact essImage_ulift_of_small (F.obj T))

/-- Genuine natural isomorphism, with every original test/map retained. -/
def smallPresheafIso (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (h : ∀ T, Small.{u} (F.obj T)) :
    smallPresheaf K F h ⋙ uliftFunctor.{u+1, u} ≅ F :=
  Functor.essImage.liftFunctorCompIso F uliftFunctor.{u+1, u} (fun T => by
    let : Small.{u} (F.obj T) := h T
    exact essImage_ulift_of_small (F.obj T))

/-- The actual original sheaf, without an original small-universe
sheafification assumption. -/
def smallSheaf (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F) (h : ∀ T, Small.{u} (F.obj T)) :
    Sheaf (topology K) (Type u) :=
  ⟨smallPresheaf K F h,
    Presheaf.isSheaf_of_isSheaf_comp (topology K) _ uliftFunctor.{u+1, u}
      ((Presheaf.isSheaf_of_iso_iff (smallPresheafIso K F h)).2 hF)⟩

/-- The universe lift of that actual sheaf is the given actual sheaf. -/
def smallSheafIso (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F) (h : ∀ T, Small.{u} (F.obj T)) :
    (largeLift K).obj (smallSheaf K F hF h) ≅ (⟨F, hF⟩ : Sheaf (topology K) (Type (u+1))) :=
  ObjectProperty.isoMk _ (smallPresheafIso K F h)

/-- Actual original sheaf construction directly from the geometric atlas.
Section smallness is a proved conclusion rather than an argument. -/
def smallSheafOfAtlas (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F) (Z : M9StandaloneDraft.Schemes K)
    (a : (largeYoneda K).obj Z ⟶ F) (ha : (largeYoneda K).relativelyRepresentable a)
    (hloc : Presheaf.IsLocallySurjective (topology K) a) : Sheaf (topology K) (Type u) :=
  smallSheaf K F hF (fun T => small_obj_of_atlas K F hF Z a ha hloc T.unop)

/-- Literal all-test natural comparison for the atlas-based construction. -/
def smallSheafOfAtlasIso (F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1))
    (hF : Presheaf.IsSheaf (topology K) F) (Z : M9StandaloneDraft.Schemes K)
    (a : (largeYoneda K).obj Z ⟶ F) (ha : (largeYoneda K).relativelyRepresentable a)
    (hloc : Presheaf.IsLocallySurjective (topology K) a) :
    (largeLift K).obj (smallSheafOfAtlas K F hF Z a ha hloc) ≅
      (⟨F, hF⟩ : Sheaf (topology K) (Type (u+1))) :=
  smallSheafIso K F hF (fun T => small_obj_of_atlas K F hF Z a ha hloc T.unop)

end M9StacksIntegration.AllTestLargeSpaceShrink
