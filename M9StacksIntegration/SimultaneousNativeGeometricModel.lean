module

public import M9StacksIntegration.AllTestNativeOriginalPullbacks
public import M9StacksIntegration.AllTestNativeGeometricPointClosure

/-! Simultaneous native geometric models of equal ORIGINAL coarse values.
The original test field is arbitrary. A genuine algebraic-space fibre product
models BOTH original parameter points over the SAME bounded algebraically
closed field, with the actual coefficient map and both parameter maps retained.
No membership of the original field in the native site is assumed. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
attribute [local implicit_reducible] AlgebraicGeometry.schemeSpace
  AlgebraicGeometry.schemeSpaceMap

namespace M9Native.SimultaneousNativeGeometricModel
open M9StacksIntegration.AllTestBoundedCharts
  M9StacksIntegration.AllTestNativeOriginalFunctor
  M9StacksIntegration.AllTestNativeOriginalSchemes
  M9StacksIntegration.AllTestNativeOriginalPullbacks
  M9StacksIntegration.AllTestNativeOriginalSpace
  M9StacksIntegration.AllTestNativeGeometricPointClosure

universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K)))

/-- The actual represented original chart respects native precomposition. -/
theorem originalChart_precompose
    {M : AlgebraicSpaces B (Spec (.of K)) hK}
    {T U : BigFppfOver B (Spec (.of K)) hK}
    (a : T ⟶ U) (f : schemeSpace U ⟶ M) :
    originalChart K B hK M T (yoneda.map a ≫ f.hom) =
      yoneda.map ((boundedInclusion B K hK).map a) ≫
        originalChart K B hK M U f.hom := by
  have he : (originalSchemeIso K B hK T).inv ≫
      (originalPresheafFunctor K B hK).map (schemeSpaceMap a) =
      yoneda.map ((boundedInclusion B K hK).map a) ≫
        (originalSchemeIso K B hK U).inv := by
    calc
      (originalSchemeIso K B hK T).inv ≫
          (originalPresheafFunctor K B hK).map (schemeSpaceMap a) =
          ((originalSchemeIso K B hK T).inv ≫
            ((originalPresheafFunctor K B hK).map (schemeSpaceMap a) ≫
              (originalSchemeIso K B hK U).hom)) ≫
                (originalSchemeIso K B hK U).inv := by
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = ((originalSchemeIso K B hK T).inv ≫
          ((originalSchemeIso K B hK T).hom ≫
            yoneda.map ((boundedInclusion B K hK).map a))) ≫
              (originalSchemeIso K B hK U).inv := by
        rw [originalSchemeIso_naturality K B hK a]
      _ = _ := by rw [Iso.inv_hom_id_assoc]
  change (originalSchemeIso K B hK T).inv ≫
      (originalPresheafFunctor K B hK).map (schemeSpaceMap a ≫ f) = _
  rw [Functor.map_comp, ← Category.assoc, he, Category.assoc]
  rfl

/-- Equality of the actual original charts reflects equality of native maps. -/
theorem native_eq_of_originalChart_eq
    {M : AlgebraicSpaces B (Spec (.of K)) hK}
    {T : BigFppfOver B (Spec (.of K)) hK}
    (f g : schemeSpace T ⟶ M)
    (h : originalChart K B hK M T f.hom = originalChart K B hK M T g.hom) :
    f = g := by
  apply (originalPresheafFullyFaithful K B hK).map_injective
  exact (cancel_epi (originalSchemeIso K B hK T).inv).mp h

/-- Two arbitrary original geometric parameter points with the same actual
coarse value descend SIMULTANEOUSLY to one native algebraically closed field.
The two native parameter points have exactly equal coarse maps, and their
extensions along the SAME original coefficient map are the original points. -/
theorem exists_simultaneous_model
    (M : AlgebraicSpaces B (Spec (.of K)) hK)
    (U V : BigFppfOver B (Spec (.of K)) hK)
    (f : yoneda.obj U ⟶ M.obj) (g : yoneda.obj V ⟶ M.obj)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L]
    (x : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj U)
    (y : M9StandaloneDraft.FieldPoint K L ⟶ (boundedInclusion B K hK).obj V)
    (hxy : (originalChart K B hK M U f).app
        (op (M9StandaloneDraft.FieldPoint K L)) x =
      (originalChart K B hK M V g).app
        (op (M9StandaloneDraft.FieldPoint K L)) y) :
    ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω)
      (hΩ : B.Contains (Spec (.of Ω))) (sΩ : Spec (.of Ω) ⟶ Spec (.of K))
      (a : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ U)
      (b : siteObject B (Spec (.of K)) hK hΩ sΩ ⟶ V)
      (w : M9StandaloneDraft.FieldPoint K L ⟶
        (boundedInclusion B K hK).obj (siteObject B (Spec (.of K)) hK hΩ sΩ)),
      yoneda.map a ≫ f = yoneda.map b ≫ g ∧
      w ≫ (boundedInclusion B K hK).map a = x ∧
      w ≫ (boundedInclusion B K hK).map b = y := by
  let fS : schemeSpace U ⟶ M := ObjectProperty.homMk f
  let gS : schemeSpace V ⟶ M := ObjectProperty.homMk g
  let P : AlgebraicSpaces B (Spec (.of K)) hK :=
    ⟨CategoryTheory.Limits.pullback f g,
      isAlgebraicSpace_pullback B (Spec (.of K)) hK f g
        (schemeSpace U).property (schemeSpace V).property M.property⟩
  let p₁ : P ⟶ schemeSpace U := ObjectProperty.homMk (pullback.fst f g)
  let p₂ : P ⟶ schemeSpace V := ObjectProperty.homMk (pullback.snd f g)
  let O := originalPresheafFunctor K B hK
  let eU := originalSchemeIso K B hK U
  let eV := originalSchemeIso K B hK V
  let ox := yoneda.map x ≫ eU.inv
  let oy := yoneda.map y ≫ eV.inv
  have hw : ox ≫ O.map fS = oy ≫ O.map gS := by
    apply yonedaEquiv.injective
    change (O.map fS).app _ (eU.inv.app _ x) = (O.map gS).app _ (eV.inv.app _ y)
    exact hxy
  have hp := original_isPullback K B hK p₁ p₂ fS gS
    (IsPullback.of_hasPullback f g)
  let z := hp.lift ox oy hw
  let zL := z.app (op (M9StandaloneDraft.FieldPoint K L)) (𝟙 _)
  obtain ⟨q, w, hq⟩ := exists_bounded_native_geometric_model K B hK
    P.obj P.property L zL
  let Q := q.val.siteObject
  let zq : (O.obj P).obj (op ((boundedInclusion B K hK).obj Q)) :=
    (M9StacksIntegration.AllTestBoundedOriginalRecovery.originalNativeRestrictionSmallIso
    K B hK P.obj P.property).inv.app (op Q) q.val.value
  let a₀ := eU.hom.app (op ((boundedInclusion B K hK).obj Q))
    ((O.map p₁).app (op ((boundedInclusion B K hK).obj Q)) zq)
  let b₀ := eV.hom.app (op ((boundedInclusion B K hK).obj Q))
    ((O.map p₂).app (op ((boundedInclusion B K hK).obj Q)) zq)
  let a := boundedPreimage B K hK a₀
  let b := boundedPreimage B K hK b₀
  have ha : (boundedInclusion B K hK).map a = a₀ := rfl
  have hb : (boundedInclusion B K hK).map b = b₀ := rfl
  have hab : schemeSpaceMap a ≫ fS = schemeSpaceMap b ≫ gS := by
    apply native_eq_of_originalChart_eq K B hK
    change originalChart K B hK M Q (yoneda.map a ≫ fS.hom) =
      originalChart K B hK M Q (yoneda.map b ≫ gS.hom)
    rw [originalChart_precompose K B hK a fS, originalChart_precompose K B hK b gS]
    apply yonedaEquiv.injective
    have ht := congrArg (fun m => m.app
      (op ((boundedInclusion B K hK).obj Q)) zq) hp.w
    change (O.map fS).app _
        (eU.inv.app _ (eU.hom.app _ ((O.map p₁).app _ zq))) =
      (O.map gS).app _ (eV.inv.app _ (eV.hom.app _ ((O.map p₂).app _ zq)))
    calc
      (O.map fS).app _ (eU.inv.app _ (eU.hom.app _ ((O.map p₁).app _ zq))) =
          (O.map fS).app _ ((O.map p₁).app _ zq) :=
        congrArg _ (Iso.hom_inv_id_apply (eU.app _) _)
      _ = (O.map gS).app _ ((O.map p₂).app _ zq) := ht
      _ = (O.map gS).app _ (eV.inv.app _ (eV.hom.app _ ((O.map p₂).app _ zq))) :=
        (congrArg _ (Iso.hom_inv_id_apply (eV.app _) _)).symm
  have hx : w ≫ (boundedInclusion B K hK).map a = x := by
    have hz : z ≫ (O.map p₁ ≫ eU.hom) = yoneda.map x := by
      rw [← Category.assoc, hp.lift_fst]
      simp only [ox, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have ht := congrArg (fun m => m.app (op (M9StandaloneDraft.FieldPoint K L)) (𝟙 _)) hz
    have hn := NatTrans.naturality_apply (O.map p₁ ≫ eU.hom) w.op zq
    change (O.map p₁ ≫ eU.hom).app (op (M9StandaloneDraft.FieldPoint K L))
      ((O.obj P).map w.op zq) = w ≫ a₀ at hn
    rw [ha]
    calc
      w ≫ a₀ = (O.map p₁ ≫ eU.hom).app _ ((O.obj P).map w.op zq) := hn.symm
      _ = (O.map p₁ ≫ eU.hom).app _ zL := congrArg _ hq
      _ = x := by
        change (O.map p₁ ≫ eU.hom).app _ zL = x at ht
        exact ht
  have hy : w ≫ (boundedInclusion B K hK).map b = y := by
    have hz : z ≫ (O.map p₂ ≫ eV.hom) = yoneda.map y := by
      rw [← Category.assoc, hp.lift_snd]
      simp only [oy, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have ht := congrArg (fun m => m.app (op (M9StandaloneDraft.FieldPoint K L)) (𝟙 _)) hz
    have hn := NatTrans.naturality_apply (O.map p₂ ≫ eV.hom) w.op zq
    change (O.map p₂ ≫ eV.hom).app (op (M9StandaloneDraft.FieldPoint K L))
      ((O.obj P).map w.op zq) = w ≫ b₀ at hn
    rw [hb]
    calc
      w ≫ b₀ = (O.map p₂ ≫ eV.hom).app _ ((O.obj P).map w.op zq) := hn.symm
      _ = (O.map p₂ ≫ eV.hom).app _ zL := congrArg _ hq
      _ = y := by
        change (O.map p₂ ≫ eV.hom).app _ zL = y at ht
        exact ht
  exact ⟨q.val.carrier, inferInstance, q.property, q.val.contained,
    q.val.toBase, a, b, w, congrArg (fun m => m.hom) hab, hx, hy⟩

end M9Native.SimultaneousNativeGeometricModel
