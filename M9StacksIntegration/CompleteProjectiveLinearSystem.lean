module

public import M9StacksIntegration.CurvePlaneLinearSystem

/-!
# A complete system gives its exact-dimensional projective embedding

The actual degree-two criterion is applied to a basis indexed by
Fin(n+1), preserving the original morphism to Spec k and the actual
pullback of O(1). In particular nine canonical sections give P⁸ rather
than a projective space obtained by padding with a zero section.

This generalizes the checked exact-three-section plane construction.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CompleteProjectiveLinearSystem

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native closed immersion attached to an exact complete basis,
including its actual over-field identity and pullback of O(1). -/
theorem exists_closedImmersion_of_h0_eq_and_degree_two_separation
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (n : ℕ) (h0 : Module.finrank k (cohomologyOverField k f L 0) = n + 1)
    (hsurj : SurjectsOnDegreeTwo f L) :
    ∃ φ : X ⟶ projectiveSpaceOver n (Spec (.of k)),
      IsClosedImmersion φ ∧
      φ ≫ Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k)) = f ∧
      Nonempty ((Scheme.Modules.pullback φ).obj
        (Stacks.AmpleProjectiveImmersion.projectiveSpaceTwistingSheaf n (Spec (.of k))) ≅ L) := by
  classical
  let : Stacks.Ample.IsInvertibleModule X L := hL
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap f)
  have hr : Module.finrank k Γ(L, ⊤) = n + 1 := by
    change Module.finrank k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)) = n + 1
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop :=
      (Scheme.Hom.app_eq_appLE f).symm
    rw [← htop]
    exact (cohomologyOverFieldZeroLinearIso k f L).toLinearEquiv.finrank_eq.symm.trans h0
  let : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper f L
  let b : Module.Basis (Fin (n + 1)) k Γ(L, ⊤) := Module.finBasisOfFinrankEq k Γ(L, ⊤) hr
  let t : Fin (n + 1) → Γ(L, ⊤) := b
  have ht : Stacks.ProjectiveFromSections.GeneratesStalks t := by
    rw [← Stacks.ProjectiveFromSections.generatesStalks_ulift_iff]
    refine generatesStalks_of_span_eq_top f L _ (fun σ => ?_)
      (generatesStalks_id_of_surjectsOnDegreeTwo f L hsurj)
    exact Submodule.span_mono
      (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (b.mem_span σ)
  obtain ⟨φ, hφ, α, hαiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse t ht f
  let := hαiso
  let g := projectiveSpaceOver.toIntegralAtUniverse n (Spec (.of k))
  let e := (Scheme.Modules.pullbackComp φ g).app
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n) ≪≫ asIso α
  let : IsProper (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) :=
    projectiveSpaceOver_isProper n (Spec (.of k))
  refine ⟨φ, ?_, hφ, ⟨e⟩⟩
  refine isClosedImmersion_of_pinned_of_span f
    (Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k))) φ hφ _ L e
    (fun i : ULift.{u} (Fin (n + 1)) =>
      Stacks.TwistPullbackPinned.pullbackCoordSection g i.down)
    (fun i : ULift.{u} (Fin (n + 1)) => t i.down) (fun i => ?_) (fun σ => ?_) hsurj
  · rw [← hα i.down, pullbackCoordSection_eq, pullbackCoordSection_eq,
      ← pullbackSectionTop_comp φ g (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)
        (Stacks.TwistPullbackPinned.coordGlobalSection n i.down)]
    exact congrArg (fun y => (Scheme.Modules.Hom.app α ⊤) y)
      (Scheme.Modules.hom_app_inv_app ((Scheme.Modules.pullbackComp φ g).app
        (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse n)) (op ⊤) _)
  · exact Submodule.span_mono
      (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (b.mem_span σ)

/-- The same actual embedding in the literal polynomial Proj model,
with the original structure morphism preserved. -/
theorem exists_polynomialProjClosedImmersion_of_h0_eq_and_degree_two_separation
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (n : ℕ) (h0 : Module.finrank k (cohomologyOverField k f L 0) = n + 1)
    (hsurj : SurjectsOnDegreeTwo f L) :
    ∃ φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k),
      IsClosedImmersion φ ∧ φ ≫ projToSpecCoeff k n = f := by
  obtain ⟨φ, hφclosed, hφ, _hL⟩ :=
    exists_closedImmersion_of_h0_eq_and_degree_two_separation f L n h0 hsurj
  let := hφclosed
  let pc := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k n
  have hbase : pc.iso.hom ≫ projToSpecCoeff k n =
      Stacks.Tag01VT.projectiveSpaceHom n (Spec (.of k)) := pc.toBase
  refine ⟨φ ≫ pc.iso.hom, inferInstance, ?_⟩
  rw [Category.assoc, hbase]
  exact hφ

end M9Native.CompleteProjectiveLinearSystem
