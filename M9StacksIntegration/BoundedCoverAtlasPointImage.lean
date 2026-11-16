module

public import M9StacksIntegration.BoundedCoverAtlasPullback

/-! The actual native comparison point belongs to the actual original
parameter image, through the derived equality of the target atlas base. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.BoundedCoverAtlasPointImage

open BoundedCoverAtlasPullback

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)
  (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (D : BoundedCoverFamily B K) {V : BigFppfOver B (Spec (.of K)) hK}
  (b : Stack.schemeStack.{u,u+1} B (Spec (.of K)) hK V ⟶
    CoverFamilyStackPullback.sourceStack B hZ K hK)

abbrev targetBaseEquality :
    B.inclusion.obj (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left =
      B.inclusion.obj V.left :=
  congrArg (fun T : BigFppfOver B integerBase hZ => B.inclusion.obj T.left)
    (NativeCoverFamilyAtlasArrow.targetFamily_base B hZ K hK V b)

variable {T : BigFppfOver B (Spec (.of K)) hK}
  (F : CoverFamilyStackPullback.PointData B hZ K hK (sourceBase B K hK D) V
    (classifier B hZ K hK D) b (P := T))

/-- The actual target comparison point, read on the actual original
base of its projected curve family. -/
abbrev targetPoint : B.inclusion.obj T.left ⟶
    B.inclusion.obj (NativeCoverFamilyAtlasArrow.targetFamily B hZ K hK V b).base.left :=
  B.inclusion.map F.right.left ≫ eqToHom (targetBaseEquality B hZ K hK b).symm

/-- The actual representing scheme and actual universal comparison
force the original target point into the genuine original family image. -/
theorem targetPoint_mem_range (E : BoundedCoverAtlasPullback.Data B hZ K hK D b)
    (t : B.inclusion.obj T.left) :
    (targetPoint B hZ K hK D b F) t ∈
      Set.range (B.inclusion.map E.familyArrow.baseMap.left).base := by
  obtain ⟨w,_,hr⟩ := E.covers_native_point F
  have hβ : B.inclusion.map E.familyArrow.baseMap.left ≫
      eqToHom (targetBaseEquality B hZ K hK b) = B.inclusion.map E.point.right.left :=
    NativeCoverFamilyAtlasArrow.familyArrow_base B hZ K hK (sourceBase B K hK D) V
      (sourceProjection B hZ K hK D) (source_schemeCurve B hZ K hK D) b E.point
  have hwright : B.inclusion.map w.left ≫ B.inclusion.map E.point.right.left =
      B.inclusion.map F.right.left := by
    simpa only [Over.comp_left, Functor.map_comp] using
      congrArg (fun a => B.inclusion.map a.left) hr
  have hw : B.inclusion.map w.left ≫ B.inclusion.map E.familyArrow.baseMap.left =
      targetPoint B hZ K hK D b F := by
    apply (cancel_mono (eqToHom (targetBaseEquality B hZ K hK b))).mp
    calc
      _ = B.inclusion.map w.left ≫ B.inclusion.map E.point.right.left := by
        rw [Category.assoc,hβ]
      _ = B.inclusion.map F.right.left := hwright
      _ = targetPoint B hZ K hK D b F ≫ eqToHom (targetBaseEquality B hZ K hK b) := by
        simp only [targetPoint, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  refine ⟨(B.inclusion.map w.left) t,?_⟩
  change (B.inclusion.map w.left ≫ B.inclusion.map E.familyArrow.baseMap.left) t = _
  rw [hw]

end M9Native.BoundedCoverAtlasPointImage
end
