module

public import M9StacksIntegration.OriginalClassifierNativeCompatibility
public import M9StacksIntegration.AllTestAffineClassifierExtension
public import M9StacksIntegration.AllTestNativeGeometricPointClosure
public import M9StacksIntegration.ASClassifierGeometricLift
public import StacksFrontier.AlgebraicGeometry.Stacks.KeelMoriEtaleLocal.GeometricPoints

/-! All-original geometric surjectivity from an actual native universal
homeomorphism. The original classifier is genuinely compared on its
actual source functor, not assumed surjective or geometrically coarse.
The original algebraically closed test field need not lie in the site. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.PresheafOfCategories
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace M9StacksIntegration.AllOriginalClassifierSurjectivity
open AllTestOriginalFamilyCategory AllTestClassifierSections AllTestBoundedCharts
  AllTestBoundedOriginalRecovery AllTestNativeOriginalFunctor AllTestNativeOriginalSpace
  AllTestAffineClassifierExtension AllTestFamilyPullback AllTestNativeGeometricPointClosure
  OriginalClassifierNativeRestriction OriginalClassifierNativeCompatibility

universe u
variable (K : Type u) [Field K] (B : BigFppfSite.{u})
  (hK : B.Contains (Spec (.of K))) (g : ℕ)
  (𝒴 : Stack.AlgebraicStacks.{u, u+1} B (Spec (.of K)) hK)
  (Φ : 𝒴.val.val.obj ⥤ CurveObject K g)
  (hΦ : Φ ⋙ projection K g = 𝒴.val.val.p ⋙ boundedInclusion B K hK)
  (M : AlgebraicSpaces B (Spec (.of K)) hK)
  (c : M9StandaloneDraft.Classifier K g ((originalPresheafFunctor K B hK).obj M))

/-- The actual original base of each source family. -/
abbrev sourceBaseEq (x : 𝒴.val.val.obj) :
    (Φ.obj x).base = (boundedInclusion B K hK).obj (𝒴.val.val.p.obj x) :=
  Functor.congr_obj hΦ x

/-- The same original family transported along its derived base isomorphism. -/
def sourceFamily (x : 𝒴.val.val.obj) :
    M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj (𝒴.val.val.p.obj x)) g :=
  pullbackFamily K (Φ.obj x).family (eqToHom (sourceBaseEq K B hK g 𝒴 Φ hΦ x).symm)

/-- This transport uses the original classifier's own Cartesian naturality. -/
theorem sourceFamily_value (x : 𝒴.val.val.obj) :
    c.value _ (sourceFamily K B hK g 𝒴 Φ hΦ x) =
      ((originalPresheafFunctor K B hK).obj M).map
        (eqToHom (sourceBaseEq K B hK g 𝒴 Φ hΦ x).symm).op
        (c.value (Φ.obj x).base (Φ.obj x).family) :=
  (c.naturality _ _ _ _ _ _ (pullbackFamily_isPullback K _ _)).symm

private theorem transport_app {C : Type*} [Category C] {E : Type*} [Category E]
    {Q R : C ⥤ E} (h : Q = R) (F : E ⥤ Type u) (x : C) :
    (eqToHom (congrArg (fun q => q ⋙ F) h)).app x =
      F.map (eqToHom (Functor.congr_obj h x)) := by
  cases h
  change 𝟙 (F.obj (Q.obj x)) = F.map (𝟙 (Q.obj x))
  exact (F.map_id (Q.obj x)).symm

/-- The named native value is the actual recovery of the transported
original family value; the base and coefficient maps have not been lost. -/
theorem nativeValue_sourceFamily (x : 𝒴.val.val.obj) :
    nativeValue K B hK g 𝒴.val.val.p Φ hΦ M c x =
      (originalNativeRestrictionSmallIso K B hK M.obj M.property).hom.app
        (op (𝒴.val.val.p.obj x))
        (c.value _ (sourceFamily K B hK g 𝒴 Φ hΦ x)) := by
  rw [sourceFamily_value, nativeValue_recovery]
  let H := (originalPresheafFunctor K B hK).obj M
  have ht := transport_app (congrArg (fun q => q.op) hΦ) H (op x)
  change (originalNativeRestrictionSmallIso K B hK M.obj M.property).hom.app _
      ((eqToHom (congrArg (fun q => q ⋙ H) (congrArg (fun q => q.op) hΦ))).app
        (op x) (c.value (Φ.obj x).base (Φ.obj x).family)) = _
  congr 1
  rw [ht]
  congr 1
  simp only [H, eqToHom_op, eqToHom_map]

variable (f : 𝒴 ⟶ Stack.algebraicSpaceStack.{u,u+1} B (Spec (.of K)) hK M.obj M.property)

/-- A vertical native comparison gives equality of the actual discrete-target functors. -/
theorem nativeFunctor_eq
    (η : classifier K B hK g 𝒴.val.val.p Φ hΦ M c ⟶
      M9Native.ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK f) :
    (classifier K B hK g 𝒴.val.val.p Φ hΦ M c).toFunctor = f.hom.hom.toFunctor :=
  eq_of_vertical_natTrans
    (classifier K B hK g 𝒴.val.val.p Φ hΦ M c).w f.hom.hom.w
    η.toNatTrans (fun x => η.isHomLift' x)

/-- An actual native image object is represented by an original family
with exactly its original recovery-unit value. -/
theorem exists_family_of_native_image
    (η : classifier K B hK g 𝒴.val.val.p Φ hΦ M c ⟶
      M9Native.ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK f)
    (V : BigFppfOver B (Spec (.of K)) hK) (n : M.obj.obj (op V))
    (x : 𝒴.val.val.obj) (hx : 𝒴.val.val.p.obj x = V)
    (hfx : f.hom.hom.obj x = ⟨V, Discrete.mk n⟩) :
    ∃ F : M9StandaloneDraft.Family K ((boundedInclusion B K hK).obj V) g,
      c.value _ F = (originalNativeRestrictionSmallIso K B hK M.obj M.property).inv.app
        (op V) n := by
  subst V
  have ho := (Functor.congr_obj (nativeFunctor_eq K B hK g 𝒴 Φ hΦ M c f η) x).trans hfx
  have hn : nativeValue K B hK g 𝒴.val.val.p Φ hΦ M c x = n := by
    change (⟨𝒴.val.val.p.obj x, Discrete.mk
      (nativeValue K B hK g 𝒴.val.val.p Φ hΦ M c x)⟩ :
        (presheafOfCategories (M.obj ⋙ typeToCat)).obj) =
      ⟨𝒴.val.val.p.obj x, Discrete.mk n⟩ at ho
    exact elementOf_congr (F := M.obj)
      (X := ⟨𝒴.val.val.p.obj x, Discrete.mk
        (nativeValue K B hK g 𝒴.val.val.p Φ hΦ M c x)⟩)
      (Y := ⟨𝒴.val.val.p.obj x, Discrete.mk n⟩)
      (V := 𝒴.val.val.p.obj x) rfl rfl ho
  refine ⟨sourceFamily K B hK g 𝒴 Φ hΦ x, ?_⟩
  have h := congrArg
    ((originalNativeRestrictionSmallIso K B hK M.obj M.property).inv.app
      (op (𝒴.val.val.p.obj x))) hn
  rw [nativeValue_sourceFamily] at h
  exact (Iso.hom_inv_id_apply
    ((originalNativeRestrictionSmallIso K B hK M.obj M.property).app _) _).symm.trans h

/-- An actual native UH and actual source compatibility imply surjectivity
on EVERY original algebraically closed extension field, without ContainsL. -/
theorem surjective_value
    (hf : Stack.UniversalHomeomorphism B (Spec (.of K)) hK f)
    (η : classifier K B hK g 𝒴.val.val.p Φ hΦ M c ⟶
      M9Native.ASClassifierGeometricLift.coarseFunctor B (Spec (.of K)) hK f)
    (L : Type u) [Field L] [Algebra K L] [IsAlgClosed L] :
    Function.Surjective (c.value (M9StandaloneDraft.FieldPoint K L)) := by
  intro z
  obtain ⟨q, w, hw⟩ := exists_bounded_native_geometric_model K B hK M.obj M.property L z
  letI : IsAlgClosed q.val.carrier := q.property
  obtain ⟨x, hx, hfx⟩ := Stack.exists_obj_of_universalHomeomorphism_algebraicSpace
    f hf q.val.carrier q.val.siteObject (Iso.refl _) q.val.value
  obtain ⟨Fq, hFq⟩ := exists_family_of_native_image K B hK g 𝒴 Φ hΦ M c f η
    q.val.siteObject q.val.value x hx hfx
  refine ⟨pullbackFamily K Fq w, ?_⟩
  calc
    c.value _ (pullbackFamily K Fq w) =
        ((originalPresheafFunctor K B hK).obj M).map w.op (c.value _ Fq) :=
      (c.naturality _ _ w _ _ _ (pullbackFamily_isPullback K Fq w)).symm
    _ = _ := by rw [hFq]; exact hw

end M9StacksIntegration.AllOriginalClassifierSurjectivity
