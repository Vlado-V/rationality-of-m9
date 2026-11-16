module

public import M9StacksIntegration.SchemeMorphismSourceH1Map

/-!
# Changing only the actual target marking of a morphism deformation

The total family, both total spaces and the deformed morphism stay the
original ones. A genuine isomorphism of special-fibre targets changes
only their marking. Source forgetting is literally unchanged.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Deformation
open Deformation.Examples

universe u

namespace M9Native.SchemeMorphismTargetMarking

variable {k : Type u} [Field k] {X Y Z : Scheme.{u}}
  (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
  (pZ : Z ⟶ Spec (.of k)) (g : X ⟶ Y) (hg : g ≫ pY = pX)
  (e : Y ≅ Z) (he : e.hom ≫ pZ = pY)

include hg he in
/-- The retargeted original morphism has the same actual structural map. -/
theorem retarget_over : (g ≫ e.hom) ≫ pZ = pX := by rw [Category.assoc, he, hg]

include he in
/-- The inverse isomorphism also retains the actual base map. -/
theorem inverse_over : e.inv ≫ pY = pZ := by
  rw [← he, Iso.inv_hom_id_assoc]

/-- Retargeting uses the same total family, changing only the target marking. -/
def retarget
    (P : schemeMorphismDeformationCategory (Λ := k) g pX pY hg) :
    schemeMorphismDeformationCategory (Λ := k) (g ≫ e.hom) pX pZ
      (retarget_over pX pY pZ g hg e he) :=
  Over.mk
    ({ base := P.hom.base
       source := P.hom.source
       target := e.inv ≫ P.hom.target
       source_pullback := by
         change IsPullback (g ≫ e.hom) P.hom.source
           (e.inv ≫ P.hom.target) P.left.morphism
         have h₀ : IsPullback (g ≫ e.hom) (𝟙 X) e.inv g :=
           IsPullback.of_vert_isIso ⟨by simp⟩
         simpa only [Category.id_comp] using h₀.paste_vert P.hom.source_pullback
       target_pullback := by
         change IsPullback (e.inv ≫ P.hom.target) pZ P.left.targetToBase
           (baseSpecMap P.hom.base)
         have h₀ : IsPullback e.inv pZ pY (𝟙 _) :=
           IsPullback.of_horiz_isIso ⟨by
             rw [inverse_over pY pZ e he, Category.comp_id]⟩
         simpa only [Category.id_comp] using h₀.paste_horiz P.hom.target_pullback } :
      P.left ⟶ schemeMorphismFamilySpecialFiber (Λ := k)
        (g ≫ e.hom) pX pZ (retarget_over pX pY pZ g hg e he))

/-- No extension of the target isomorphism to a deformed target is used. -/
theorem retarget_total
    (P : schemeMorphismDeformationCategory (Λ := k) g pX pY hg) :
    (retarget pX pY pZ g hg e he P).left = P.left := rfl

/-- The source deformation is exactly the original source deformation. -/
theorem sourceForgetful_retarget
    (P : schemeMorphismDeformationCategory (Λ := k) g pX pY hg) :
    (schemeMorphismSourceForgetful (Λ := k) (g ≫ e.hom) pX pZ
      (retarget_over pX pY pZ g hg e he)).obj (retarget pX pY pZ g hg e he P) =
      (schemeMorphismSourceForgetful (Λ := k) g pX pY hg).obj P := rfl

/-- The same construction in the original fibre over the same Artinian algebra. -/
def retargetFibre (A : ArtinianLocalAlgCat.{u,u,u} k k)
    (z : (schemeMorphismDeformationCategoryProjection (Λ := k) g pX pY hg).Fiber A) :
    (schemeMorphismDeformationCategoryProjection (Λ := k) (g ≫ e.hom) pX pZ
      (retarget_over pX pY pZ g hg e he)).Fiber A :=
  ⟨retarget pX pY pZ g hg e he z.val, z.property⟩

/-- Source endpoint classes retain the actual coefficient module and actual class. -/
theorem sourceEndpoint_class (V : FGModuleCat.{u} k)
    (z : (schemeMorphismDeformationCategoryProjection (Λ := k) g pX pY hg).Fiber
      (coordBase (Λ := k) V)) :
    (schemeMorphismTangentPair' (Λ := k) (g ≫ e.hom) pX pZ
      (retarget_over pX pY pZ g hg e he)
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _) V
      (tangentClassAt _ (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _)
        V (retargetFibre pX pY pZ g hg e he _ z))).1 =
    (schemeMorphismTangentPair' (Λ := k) g pX pY hg
      (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _) V
      (tangentClassAt _ (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _)
        V z)).1 := by
  change tangentMapAt _ _ (schemeMorphismSourceBased (g ≫ e.hom) pX pZ
    (retarget_over pX pY pZ g hg e he)) V _ =
      tangentMapAt _ _ (schemeMorphismSourceBased g pX pY hg) V _
  rw [tangentMapAt_tangentClassAt, tangentMapAt_tangentClassAt]
  rfl

set_option maxRecDepth 1024 in
/-- The actual original source-H¹ image is contained in the retargeted image. -/
theorem sourceH1_range_le [IsCurve k pX] [Smooth pX] :
    LinearMap.range (SchemeMorphismSourceH1.sourceForgettingH1 pX pY g hg) ≤
      LinearMap.range (SchemeMorphismSourceH1.sourceForgettingH1 pX pZ
        (g ≫ e.hom) (retarget_over pX pY pZ g hg e he)) := by
  rintro v ⟨t, rfl⟩
  let V := FGModuleCat.of k (ULift.{u} k)
  let B := BasedCategory.ofFunctor
    (schemeMorphismDeformationCategoryProjection (Λ := k) g pX pY hg)
  let hB := isDeformationCategory_schemeMorphismDeformationCategoryProjection (Λ := k)
    g pX pY hg
  obtain ⟨z, rfl⟩ := tangentClassAt_surjective B hB V t
  refine ⟨tangentClassAt _
    (isDeformationCategory_schemeMorphismDeformationCategoryProjection _ _ _ _) V
    (retargetFibre pX pY pZ g hg e he _ z), ?_⟩
  exact congrArg (StandardSchemeTangent.endpointTangentLinearEquivH1 (Λ := k) pX)
    (sourceEndpoint_class pX pY pZ g hg e he V z)

end M9Native.SchemeMorphismTargetMarking
