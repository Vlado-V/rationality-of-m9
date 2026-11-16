module

public import M9StacksIntegration.AllTestBoundedOriginalRecovery
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Points

/-!
# Bounded native field models of ALL original geometric points

An actual original section over ANY algebraically closed extension field
lifts to an actual original surjective-etale chart. The SAME bounded atlas
of the constructed original space then supplies an actual native field
model: the residue field of its atlas point. Its spectrum lies in the
chosen native site, and its actual original scalar map to the extension
field recovers the original section. There is NO containment hypothesis
on that original extension field and no assumed classification/equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeGeometricPointModel
open AllTestBoundedCharts AllTestNativeOriginalSpace
  AllTestNativeOriginalAtlas AllTestBoundedOriginalRecovery
universe u
variable (K : Type u) [Field K]

/-- Every ORIGINAL geometric section lifts through an ACTUAL original
represented surjective-etale morphism, with the SAME coefficient map. -/
theorem exists_lift_of_etale_surjective
    {M : M9StandaloneDraft.Presheaves K} {U : M9StandaloneDraft.Schemes K}
    (a : yoneda.obj U ⟶ M)
    (he : (MorphismProperty.inverseImage (@Etale.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (hs : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget (M9StandaloneDraft.Base K))).presheaf a)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : M.obj (op (M9StandaloneDraft.FieldPoint K L))) :
    ∃ b : M9StandaloneDraft.FieldPoint K L ⟶ U,
      a.app (op (M9StandaloneDraft.FieldPoint K L)) b = x := by
  let T := M9StandaloneDraft.FieldPoint K L
  let α : yoneda.obj T ⟶ M := yonedaEquiv.symm x
  let V := he.rep.pullback α
  let b : V ⟶ U := he.rep.fst' α
  let q : V ⟶ T := he.rep.snd α
  have hcart : IsPullback (yoneda.map b) (yoneda.map q) a α := he.rep.isPullback' α
  let : Etale q.left := he.property α (yoneda.map b) q hcart
  let : Surjective q.left := hs.property α (yoneda.map b) q hcart
  obtain ⟨y, _⟩ := q.left.surjective (IsLocalRing.closedPoint L)
  let : Nonempty V.left := ⟨y⟩
  let : JacobsonSpace T.left := by
    change JacobsonSpace (Spec (.of L))
    infer_instance
  let : JacobsonSpace V.left := LocallyOfFiniteType.jacobsonSpace q.left
  obtain ⟨z, _, hz⟩ := nonempty_inter_closedPoints
    (X := V.left) (Z := Set.univ) Set.univ_nonempty isOpen_univ.isLocallyClosed
  let σ : Spec (.of L) ⟶ V.left := pointOfClosedPoint q.left z hz
  have hσ : σ ≫ q.left = 𝟙 (Spec (.of L)) := pointOfClosedPoint_comp q.left z hz
  let r : T ⟶ V := Over.homMk σ (by
    rw [← Over.w q, ← Category.assoc, hσ]
    exact Category.id_comp T.hom)
  have hr : r ≫ q = 𝟙 T := Over.OverMorphism.ext hσ
  have hba : yoneda.map (r ≫ b) ≫ a = α := by
    rw [(yoneda (C := M9StandaloneDraft.Schemes K)).map_comp, Category.assoc,
      hcart.w, ← Category.assoc,
      ← (yoneda (C := M9StandaloneDraft.Schemes K)).map_comp, hr,
      (yoneda (C := M9StandaloneDraft.Schemes K)).map_id, Category.id_comp]
  refine ⟨r ≫ b, ?_⟩
  have h := congrArg yonedaEquiv hba
  have h' : a.app (op T) (r ≫ b) = yonedaEquiv α := by
    simpa only [yonedaEquiv_comp, yonedaEquiv_yoneda_map] using h
  exact h'.trans (Equiv.apply_symm_apply yonedaEquiv x)

/-- EVERY original geometric point of an actual native space's full-site
extension comes from an ACTUAL native field-valued point. The actual map
of original field spectra retains its coefficient structure; the original
extension field is not required to belong to the native site. -/
theorem exists_bounded_native_field_model
    (B : BigFppfSite.{u}) (hK : B.Contains (Spec (.of K)))
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : (originalSpaceOfNative K B hK F hF).obj.obj
      (op (M9StandaloneDraft.FieldPoint K L))) :
    ∃ (p : Space.FieldValuedPoint B (Spec (.of K)) hK F)
      (v : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj p.siteObject),
      (originalSpaceOfNative K B hK F hF).obj.map v.op
        ((originalNativeRestrictionSmallIso K B hK F hF).inv.app (op p.siteObject)
          p.value) = x := by
  let G := originalSpaceOfNative K B hK F hF
  obtain ⟨U, a, hae, has⟩ := exists_bounded_original_atlas K B hK F hF
  obtain ⟨b, hb⟩ := exists_lift_of_etale_surjective K a hae has L x
  let X := (BigFppfOver.toScheme B (Spec (.of K)) hK).obj U
  let β : Spec (.of L) ⟶ X := b.left
  let t : X := β (IsLocalRing.closedPoint L)
  let κ := X.residueField t
  let hκ : B.Contains (Spec κ) := B.residueField_spec_contains U.left.property t
  let sκ : Spec κ ⟶ Spec (.of K) := X.fromSpecResidueField t ≫ U.hom.hom
  let Tκ := siteObject B (Spec (.of K)) hK hκ sκ
  let c : (boundedInclusion B K hK).obj Tκ ⟶ (boundedInclusion B K hK).obj U :=
    Over.homMk (X.fromSpecResidueField t) rfl
  let τ : Spec (.of L) ⟶ Spec κ :=
    Spec.map (X.descResidueField (Scheme.stalkClosedPointTo β))
  have hτ : τ ≫ X.fromSpecResidueField t = β :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField L X β
  let v : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj Tκ :=
    Over.homMk τ (by
      change τ ≫ (X.fromSpecResidueField t ≫ U.hom.hom) = _
      rw [← Category.assoc, hτ]
      exact Over.w b)
  have hvc : v ≫ c = b := Over.OverMorphism.ext hτ
  let xκ : G.obj.obj (op ((boundedInclusion B K hK).obj Tκ)) := a.app _ c
  let e := originalNativeRestrictionSmallIso K B hK F hF
  let p : Space.FieldValuedPoint B (Spec (.of K)) hK F :=
    { carrier := κ
      contained := hκ
      toBase := sκ
      value := e.hom.app (op Tκ) xκ }
  refine ⟨p, v, ?_⟩
  change G.obj.map v.op (e.inv.app (op Tκ) (e.hom.app (op Tκ) xκ)) = x
  change G.obj.map v.op ((e.app (op Tκ)).inv ((e.app (op Tκ)).hom xκ)) = x
  rw [Iso.hom_inv_id_apply]
  change G.obj.map v.op (a.app _ c) = x
  rw [← NatTrans.naturality_apply a v.op]
  change a.app _ (v ≫ c) = x
  rw [hvc]
  exact hb

end M9StacksIntegration.AllTestNativeGeometricPointModel
