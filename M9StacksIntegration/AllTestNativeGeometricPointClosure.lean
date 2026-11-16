module

public import M9StacksIntegration.AllTestNativeGeometricPointModel
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldExtensionDescent.AlgebraicClosureSite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.GeometricPoints

/-!
# Native algebraically closed models compatible with ORIGINAL scalars

The algebraic closure of a native field stays in the native site. An
actual map from ANY original algebraically closed field spectrum lifts
compatibly to that algebraic closure by the genuine algebraic embedding
theorem. Thus every geometric point of the actual full-original extension
has an ACTUAL native geometric model, retaining its original coefficient
map. No field containment or geometric-classification assertion is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestNativeGeometricPointClosure
open AllTestBoundedCharts AllTestNativeOriginalSpace AllTestBoundedOriginalRecovery
  AllTestNativeGeometricPointModel
universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- A native field point has a native ALGEBRAICALLY CLOSED extension
compatible with the prescribed ORIGINAL algebraically closed field map. -/
theorem exists_compatible_geometric_extension
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (p : Space.FieldValuedPoint B (Spec (.of K)) hK F)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (v : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj p.siteObject) :
    ∃ (q : Space.GeometricPoint B (Spec (.of K)) hK F)
      (a : q.val.siteObject ⟶ p.siteObject)
      (w : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj q.val.siteObject),
      F.map a.op p.value = q.val.value ∧ w ≫ (boundedInclusion B K hK).map a = v := by
  let φ : p.carrier →+* L := (Spec.preimage v.left).hom
  let : Algebra p.carrier L := φ.toAlgebra
  let Ω := AlgebraicClosure p.carrier
  let hΩ : B.Contains (Spec (.of Ω)) := B.contains_spec_algebraicClosure p.carrier p.contained
  let f : Ω →ₐ[p.carrier] L := IsAlgClosed.lift
  let aSch : Spec (.of Ω) ⟶ Spec (.of p.carrier) :=
    Spec.map (CommRingCat.ofHom (algebraMap p.carrier Ω))
  let wSch : Spec (.of L) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom f.toRingHom)
  have hwa : wSch ≫ aSch = v.left := by
    have hφ : f.toRingHom.comp (algebraMap p.carrier Ω) = φ := by
      ext z
      exact f.commutes z
    change Spec.map (CommRingCat.ofHom f.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap p.carrier Ω)) = v.left
    rw [← Spec.map_comp]
    change Spec.map (CommRingCat.ofHom (f.toRingHom.comp (algebraMap p.carrier Ω))) = v.left
    rw [hφ]
    exact Spec.map_preimage v.left
  let TΩ := siteObject B (Spec (.of K)) hK hΩ (aSch ≫ p.toBase)
  let a : TΩ ⟶ p.siteObject :=
    Over.homMk (ObjectProperty.homMk aSch) rfl
  let q : Space.FieldValuedPoint B (Spec (.of K)) hK F :=
    { carrier := Ω
      contained := hΩ
      toBase := aSch ≫ p.toBase
      value := F.map a.op p.value }
  let w : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj q.siteObject :=
    Over.homMk wSch (by
      change wSch ≫ (aSch ≫ p.toBase) = _
      rw [← Category.assoc, hwa]
      exact Over.w v)
  exact ⟨⟨q, inferInstance⟩, a, w, rfl, Over.OverMorphism.ext hwa⟩

/-- Every geometric point on ALL original test fields is the actual
scalar extension of an ACTUAL native geometric point. There is NO
`B.Contains (Spec L)` input and no fixed restriction of the field tests. -/
theorem exists_bounded_native_geometric_model
    (F : (BigFppfOver B (Spec (.of K)) hK)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B (Spec (.of K)) hK F)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : (originalSpaceOfNative K B hK F hF).obj.obj
      (op (M9StandaloneDraft.FieldPoint K L))) :
    ∃ (q : Space.GeometricPoint B (Spec (.of K)) hK F)
      (w : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj q.val.siteObject),
      (originalSpaceOfNative K B hK F hF).obj.map w.op
        ((originalNativeRestrictionSmallIso K B hK F hF).inv.app (op q.val.siteObject)
          q.val.value) = x := by
  obtain ⟨p, v, hx⟩ := exists_bounded_native_field_model K B hK F hF L x
  obtain ⟨q, a, w, hq, hw⟩ := exists_compatible_geometric_extension K B hK F p L v
  let G := originalSpaceOfNative K B hK F hF
  let e := originalNativeRestrictionSmallIso K B hK F hF
  have he := (NatTrans.naturality_apply e.inv a.op p.value).symm
  change G.obj.map ((boundedInclusion B K hK).map a).op
      (e.inv.app (op p.siteObject) p.value) =
    e.inv.app (op q.val.siteObject) (F.map a.op p.value) at he
  refine ⟨q, w, ?_⟩
  change G.obj.map w.op (e.inv.app (op q.val.siteObject) q.val.value) = x
  rw [← hq, ← he]
  have hcomp := G.obj.map_comp ((boundedInclusion B K hK).map a).op w.op
  change G.obj.map (w ≫ (boundedInclusion B K hK).map a).op =
    G.obj.map ((boundedInclusion B K hK).map a).op ≫ G.obj.map w.op at hcomp
  rw [← ConcreteCategory.comp_apply, ← hcomp, hw]
  exact hx

end M9StacksIntegration.AllTestNativeGeometricPointClosure
