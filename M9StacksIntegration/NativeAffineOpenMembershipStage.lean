module

public import M9StacksIntegration.NativeRelativeAffineOpenStage
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceSections

/-!
# Actual eventual open-subspace membership on an affine diagram

An actual section at the limit of affine schemes lies in a genuine native
open subspace only if a later transition already lies in that subspace.
The proof passes through the corresponding ORIGINAL open subscheme and
the checked relative stage-factorization theorem. No absolute finite-type
claim, no noetherian hypothesis, and no site-equivalence premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.NativeAffineOpenMembershipStage
universe u

/-- A factorization through an actual subfunctor of a representable is
exactly membership of the actual represented morphism in that subfunctor. -/
theorem factorsThrough_subfunctor_iff
    {C : Type (u+1)} [Category.{u} C] {T V : C}
    (W : Subfunctor (yoneda.obj V)) (a : T ⟶ V) :
    (∃ t : yoneda.obj T ⟶ W.toFunctor, t ≫ W.ι = yoneda.map a) ↔
      a ∈ W.obj (op T) := by
  constructor
  · rintro ⟨t, ht⟩
    have hv : (t.app (op T) (𝟙 T)).val = a := by
      have h := congrArg (fun z : yoneda.obj T ⟶ yoneda.obj V =>
        z.app (op T) (𝟙 T)) ht
      exact h.trans (Category.id_comp a)
    exact hv ▸ (t.app (op T) (𝟙 T)).property
  · intro ha
    let t : yoneda.obj T ⟶ W.toFunctor :=
      { app := fun U => ↾fun b => ⟨b ≫ a, W.map b.op ha⟩
        naturality := fun U U' b => by
          ext f
          apply Subtype.ext
          exact Category.assoc _ _ _ }
    refine ⟨t, ?_⟩
    ext U f
    rfl

/-- Membership of the ACTUAL limit leg in an ACTUAL open subspace occurs
already for an ACTUAL transition at a later affine stage. -/
theorem exists_transition_mem_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (haff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (i : I) (W : Subfunctor (yoneda.obj (D.obj i)))
    (hW : Space.IsOpenSubspace B S hS W)
    (hmem : c.π.app i ∈ W.obj (op c.pt)) :
    ∃ (j : I) (a : j ⟶ i), D.map a ∈ W.obj (op (D.obj j)) := by
  let V := BigFppfOver.toScheme B S hS
  let U := Space.opensOfOpenSubspace B S hS (D.obj i) W hW
  have hrange : Set.range (V.map (c.π.app i)) ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact (Space.mem_iff_of_isOpenSubspace B S hS (D.obj i) W hW
      (c.π.app i)).mp hmem y
  let f : V.obj c.pt ⟶ U := IsOpenImmersion.lift U.ι (V.map (c.π.app i)) hrange
  have hf : f ≫ U.ι = V.map (c.π.app i) :=
    IsOpenImmersion.lift_fac U.ι (V.map (c.π.app i)) hrange
  obtain ⟨j, a, g, hg, _⟩ := NativeRelativeAffineOpenStage.exists_stage_factor_open
    (D ⋙ V) (V.mapCone c) hc haff i U f hf
  refine ⟨j, a, (Space.mem_iff_of_isOpenSubspace B S hS
    (D.obj i) W hW (D.map a)).mpr ?_⟩
  intro y
  change (V.map (D.map a)) y ∈ U
  change g ≫ U.ι = V.map (D.map a) at hg
  rw [← hg, Scheme.Hom.comp_apply]
  exact (g y).property

/-- The same eventual membership with a prescribed ACTUAL map from the
stage to another representable, so base-identification maps are retained. -/
theorem exists_transition_comp_mem_open
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (haff : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (i : I) {T : BigFppfOver B S hS} (a : D.obj i ⟶ T)
    (W : Subfunctor (yoneda.obj T)) (hW : Space.IsOpenSubspace B S hS W)
    (hmem : c.π.app i ≫ a ∈ W.obj (op c.pt)) :
    ∃ (j : I) (b : j ⟶ i), D.map b ≫ a ∈ W.obj (op (D.obj j)) := by
  let W' := W.preimage (yoneda.map a)
  have hW' : Space.IsOpenSubspace B S hS W' :=
    Space.isOpenSubspace_preimage B S hS (yoneda.map a) W
      (isAlgebraicSpace_yoneda B S hS T)
      (isAlgebraicSpace_yoneda B S hS (D.obj i)) hW
  exact exists_transition_mem_open B S hS D c hc haff i W' hW' hmem

end M9StacksIntegration.NativeAffineOpenMembershipStage
