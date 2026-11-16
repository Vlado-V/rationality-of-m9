module

public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import M9StacksIntegration.AllTestNativeOriginalFunctor

/-!
# The actual original/native recovery unit is natural

The proved objectwise recovery isomorphisms are compatible with EVERY
actual native algebraic-space morphism. This follows from naturality of
the actual sheaf-extension adjunction and of the actual original-value
comparison, reflected through the fully faithful universe lift.
No naturality, comparison, or family-classifier premise is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalUnit
open AllTestBoundedCharts AllTestBoundedRestriction AllTestBoundedOriginalRecovery AllTestBoundedFaithful AllTestBoundedAlgebraicSpace
  AllTestNativeOriginalFunctor AllTestNativeOriginalRestriction AllTestLargeSpaceGeometry
  AllTestLargeSitePullback AllTestNativeSpacePresentation
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The genuine small-valued recovery is exactly the preimage of its
proved large-valued adjunction comparison. -/
theorem ulift_originalNativeRestrictionSmallIso_hom
    (F : AlgebraicSpaces B (Spec (.of K)) hK) :
    Functor.whiskerRight
        (originalNativeRestrictionSmallIso K B hK F.obj F.property).hom
        uliftFunctor.{u+1, u} =
      (originalNativeRestrictionIso K B hK F.obj F.property).hom :=
  (fullyFaithfulULiftFunctor.{u+1, u}.whiskeringRight _).map_preimage _

set_option backward.defeqAttrib.useBackward true in
/-- Recovery of the SAME native object retains every ACTUAL morphism. -/
theorem originalNativeRestrictionSmallIso_naturality
    {F G : AlgebraicSpaces B (Spec (.of K)) hK} (f : F ⟶ G) :
    restrictMap K B hK ((originalPresheafFunctor K B hK).map f) ≫
        (originalNativeRestrictionSmallIso K B hK G.obj G.property).hom =
      (originalNativeRestrictionSmallIso K B hK F.obj F.property).hom ≫ f.hom := by
  apply (fullyFaithfulULiftFunctor.{u+1, u}.whiskeringRight _).map_injective
  simp only [Functor.map_comp]
  let J := BigFppfOver.topology B (Spec (.of K)) hK
  let i := (boundedInclusion B K hK).op
  let Q := nativeSheafFunctor K B hK ⋙ sheafCompose J uliftFunctor.{u+1, u}
  let e := originalComparison K B hK
  let η := extensionUnitIso K B hK
  let W := sheafToPresheaf J (Type (u+1))
  have h₁ := congrArg (fun m => Functor.whiskerLeft i m) (e.hom.naturality f)
  simp only [Functor.whiskerLeft_comp] at h₁
  have h₂ := congrArg (fun m => W.map m) (η.inv.naturality (Q.map f))
  simp only [Functor.map_comp] at h₂
  change Functor.whiskerLeft i ((valueLift K).map ((originalPresheafFunctor K B hK).map f)) ≫
      Functor.whiskerLeft i (e.app G).hom =
    Functor.whiskerLeft i (e.app F).hom ≫
      Functor.whiskerLeft i ((extendedNativePresheafFunctor K B hK).map f) at h₁
  change Functor.whiskerLeft i ((extendedNativePresheafFunctor K B hK).map f) ≫
      W.map (η.app (Q.obj G)).inv =
    W.map (η.app (Q.obj F)).inv ≫ Functor.whiskerRight f.hom uliftFunctor.{u+1, u} at h₂
  change Functor.whiskerLeft i ((valueLift K).map ((originalPresheafFunctor K B hK).map f)) ≫
      (Functor.whiskerLeft i (e.app G).hom ≫ W.map (η.app (Q.obj G)).inv) =
    (Functor.whiskerLeft i (e.app F).hom ≫ W.map (η.app (Q.obj F)).inv) ≫
      Functor.whiskerRight f.hom uliftFunctor.{u+1, u}
  calc
    _ = (Functor.whiskerLeft i ((valueLift K).map
        ((originalPresheafFunctor K B hK).map f)) ≫
        Functor.whiskerLeft i (e.app G).hom) ≫ W.map (η.app (Q.obj G)).inv :=
      (Category.assoc _ _ _).symm
    _ = (Functor.whiskerLeft i (e.app F).hom ≫
        Functor.whiskerLeft i ((extendedNativePresheafFunctor K B hK).map f)) ≫
          W.map (η.app (Q.obj G)).inv :=
      congrArg (fun m => m ≫ W.map (η.app (Q.obj G)).inv) h₁
    _ = Functor.whiskerLeft i (e.app F).hom ≫
        (Functor.whiskerLeft i ((extendedNativePresheafFunctor K B hK).map f) ≫
          W.map (η.app (Q.obj G)).inv) := Category.assoc _ _ _
    _ = Functor.whiskerLeft i (e.app F).hom ≫
        (W.map (η.app (Q.obj F)).inv ≫ Functor.whiskerRight f.hom uliftFunctor.{u+1, u}) :=
      congrArg (fun m => Functor.whiskerLeft i (e.app F).hom ≫ m) h₂
    _ = _ := (Category.assoc _ _ _).symm

/-- The ACTUAL extension followed by full-original-test restriction is
naturally the SAME native algebraic-space presheaf, with the original
Type-u section universe. -/
def originalRestrictionUnitIso :
    originalPresheafFunctor K B hK ⋙ restrictionFunctor K B hK ≅
      ObjectProperty.ι (IsAlgebraicSpace B (Spec (.of K)) hK) :=
  NatIso.ofComponents
    (fun F => originalNativeRestrictionSmallIso K B hK F.obj F.property)
    (fun f => originalNativeRestrictionSmallIso_naturality K B hK f)

end M9StacksIntegration.AllTestNativeOriginalUnit
