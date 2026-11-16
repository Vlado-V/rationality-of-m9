module

public import M9StacksIntegration.AllTestNativeOriginalRestriction
public import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Actual functorial original spaces and morphisms

The constructed original spaces carry actual morphisms obtained from the
actual sheaf extension, through the proved fully faithful value lift. The
comparison is a genuine natural isomorphism. The resulting functor is
fully faithful, proved from actual native and original sheaf functors;
no full-faithfulness or classifier premise is supplied.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeOriginalFunctor
open AllTestNativeOriginalSpace AllTestNativeOriginalRestriction
  AllTestNativeSpacePresentation AllTestLargeSitePullback AllTestLargeSpaceGeometry
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual native sheaf underlying an actual native algebraic space. -/
def nativeSheafFunctor : AlgebraicSpaces B (Spec (.of K)) hK ⥤
    Sheaf (BigFppfOver.topology B (Spec (.of K)) hK) (Type u) :=
  ObjectProperty.ιOfLE (fun _ hF => hF.isSheaf)

/-- Actual full faithfulness of the inclusion into native sheaves. -/
def nativeSheafFullyFaithful : (nativeSheafFunctor K B hK).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE (fun
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F) => hF.isSheaf)

/-- The actual full-original-site large-valued extension, on objects AND maps. -/
def extendedNativePresheafFunctor : AlgebraicSpaces B (Spec (.of K)) hK ⥤
    (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1) :=
  nativeSheafFunctor K B hK ⋙
    sheafCompose (BigFppfOver.topology B (Spec (.of K)) hK) uliftFunctor.{u+1, u} ⋙
    extendSheaf K B hK ⋙
    sheafToPresheaf (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1))

/-- An actual map between the constructed ORIGINAL spaces on all original tests. -/
def originalPresheafMap {F G : AlgebraicSpaces B (Spec (.of K)) hK} (f : F ⟶ G) :
    (originalSpaceOfNative K B hK F.obj F.property).obj ⟶
      (originalSpaceOfNative K B hK G.obj G.property).obj := by
  let : (valueLift K).Full := (valueLift_fullyFaithful K).full
  exact (valueLift K).preimage
    ((originalSpaceOfNativeIso K B hK F.obj F.property).hom ≫
      (extendedNativePresheafFunctor K B hK).map f ≫
      (originalSpaceOfNativeIso K B hK G.obj G.property).inv)

set_option backward.isDefEq.respectTransparency false in
/-- The actual original morphism has the literal extended native morphism
under the genuine original-space universe comparisons. -/
theorem valueLift_originalPresheafMap
    {F G : AlgebraicSpaces B (Spec (.of K)) hK} (f : F ⟶ G) :
    (valueLift K).map (originalPresheafMap K B hK f) ≫
        (originalSpaceOfNativeIso K B hK G.obj G.property).hom =
      (originalSpaceOfNativeIso K B hK F.obj F.property).hom ≫
        (extendedNativePresheafFunctor K B hK).map f := by
  let : (valueLift K).Full := (valueLift_fullyFaithful K).full
  dsimp only [originalPresheafMap]
  rw [(valueLift K).map_preimage]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- Native algebraic spaces and their actual maps, read on the FULL original site. -/
def originalPresheafFunctor : AlgebraicSpaces B (Spec (.of K)) hK ⥤
    M9StandaloneDraft.Presheaves K where
  obj F := (originalSpaceOfNative K B hK F.obj F.property).obj
  map f := originalPresheafMap K B hK f
  map_id F := by
    apply (valueLift_fullyFaithful K).map_injective
    rw [(valueLift K).map_id]
    apply (cancel_mono (originalSpaceOfNativeIso K B hK F.obj F.property).hom).mp
    rw [Category.id_comp]
    exact (valueLift_originalPresheafMap K B hK (𝟙 F)).trans
      ((congrArg (fun m => (originalSpaceOfNativeIso K B hK F.obj F.property).hom ≫ m)
        ((extendedNativePresheafFunctor K B hK).map_id F)).trans (Category.comp_id _))
  map_comp {F G H} f g := by
    apply (valueLift_fullyFaithful K).map_injective
    rw [(valueLift K).map_comp]
    apply (cancel_mono (originalSpaceOfNativeIso K B hK H.obj H.property).hom).mp
    rw [valueLift_originalPresheafMap, Category.assoc, valueLift_originalPresheafMap,
      ← Category.assoc, valueLift_originalPresheafMap, Category.assoc, Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- The actual original-space universe comparison is natural in every native map. -/
def originalComparison : originalPresheafFunctor K B hK ⋙ valueLift K ≅
    extendedNativePresheafFunctor K B hK :=
  NatIso.ofComponents
    (fun F => originalSpaceOfNativeIso K B hK F.obj F.property)
    (fun f => valueLift_originalPresheafMap K B hK f)

/-- Full faithfulness of the actual extension on actual native algebraic spaces. -/
def extendedNativeFullyFaithful :
    (extendedNativePresheafFunctor K B hK).FullyFaithful :=
  (nativeSheafFullyFaithful K B hK).comp
    ((fullyFaithfulSheafCompose (F := uliftFunctor.{u+1, u})
      (BigFppfOver.topology B (Spec (.of K)) hK)
      fullyFaithfulULiftFunctor).comp ((extendSheafFullyFaithful K B hK).comp
        (fullyFaithfulSheafToPresheaf
          (Scheme.fppfTopology.over (M9StandaloneDraft.Base K)) (Type (u+1)))))

/-- The actual native→original-space functor is fully faithful; no such
property is assumed in its construction or in this proof. -/
def originalPresheafFullyFaithful : (originalPresheafFunctor K B hK).FullyFaithful := by
  let : (extendedNativePresheafFunctor K B hK).Full :=
    (extendedNativeFullyFaithful K B hK).full
  let : (extendedNativePresheafFunctor K B hK).Faithful :=
    (extendedNativeFullyFaithful K B hK).faithful
  let : (valueLift K).Faithful := (valueLift_fullyFaithful K).faithful
  let : (originalPresheafFunctor K B hK).Full :=
    Functor.Full.of_comp_faithful_iso (originalComparison K B hK)
  let : (originalPresheafFunctor K B hK).Faithful :=
    Functor.Faithful.of_comp_iso (originalComparison K B hK)
  exact Functor.FullyFaithful.ofFullyFaithful _

end M9StacksIntegration.AllTestNativeOriginalFunctor
