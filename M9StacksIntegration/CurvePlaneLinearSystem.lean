module

public import M9StacksIntegration.GenusNineNotPlane
public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwoComplete
public import StacksFrontier.AlgebraicGeometry.ProjBaseChange.IsIso

/-!
# A complete three-section embedding is an actual plane embedding

The native degree-two separation criterion is applied to exactly three
complete sections, rather than to a padded basis. Its projective-space
map is transported through the actual polynomial/base-change comparison
to the literal native `Proj k[T₀,T₁,T₂]`. The native plane genus theorem
then excludes degree-two separation on a genus-nine curve.

The accompanying audit records the source-bound kernel-check status.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CurvePlaneLinearSystem

open CategoryTheory AlgebraicGeometry Opposite
open Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual line bundle with exactly three complete sections which
separates all length-two closed subschemes gives an actual plane closed
immersion over the original field. -/
theorem exists_planeClosedImmersion_of_surjectsOnDegreeTwo_of_h0_eq_three
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (h0 : Module.finrank k (cohomologyOverField k f L 0) = 3)
    (hsurj : SurjectsOnDegreeTwo f L) :
    ∃ i : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 3) k),
      IsClosedImmersion i ∧ i ≫ projToSpecCoeff k 2 = f := by
  classical
  let : Stacks.Ample.IsInvertibleModule X L := hL
  let : Module k Γ(L, ⊤) := Module.compHom _ (baseRingMap f)
  have hr : Module.finrank k Γ(L, ⊤) = 3 := by
    change Module.finrank k ((ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (op (⊤ : X.Opens))).obj L)) = 3
    have htop : f.appLE ⊤ ⊤ (by simp) = f.appTop :=
      (Scheme.Hom.app_eq_appLE f).symm
    rw [← htop]
    exact (cohomologyOverFieldZeroLinearIso k f L).toLinearEquiv.finrank_eq.symm.trans h0
  let : Module.Finite k Γ(L, ⊤) := moduleFinite_sections_of_isProper f L
  let b : Module.Basis (Fin 3) k Γ(L, ⊤) := Module.finBasisOfFinrankEq k Γ(L, ⊤) hr
  let t : Fin (2 + 1) → Γ(L, ⊤) := b
  have ht : Stacks.ProjectiveFromSections.GeneratesStalks t := by
    rw [← Stacks.ProjectiveFromSections.generatesStalks_ulift_iff]
    refine generatesStalks_of_span_eq_top f L _ (fun σ => ?_)
      (generatesStalks_id_of_surjectsOnDegreeTwo f L hsurj)
    exact Submodule.span_mono
      (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (b.mem_span σ)
  obtain ⟨φ, hφ, α, hαiso, hα⟩ :=
    Stacks.TwistPullbackPinned.exists_hom_over_and_iso_pullback_twistingSheafAtUniverse t ht f
  let := hαiso
  let g := projectiveSpaceOver.toIntegralAtUniverse 2 (Spec (.of k))
  let e := (Scheme.Modules.pullbackComp φ g).app
    (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse 2) ≪≫ asIso α
  let : IsProper (Stacks.Tag01VT.projectiveSpaceHom 2 (Spec (.of k))) :=
    projectiveSpaceOver_isProper 2 (Spec (.of k))
  have hclosed : IsClosedImmersion φ := by
    refine isClosedImmersion_of_pinned_of_span f
      (Stacks.Tag01VT.projectiveSpaceHom 2 (Spec (.of k))) φ hφ _ L e
      (fun i : ULift.{u} (Fin 3) =>
        Stacks.TwistPullbackPinned.pullbackCoordSection g i.down)
      (fun i : ULift.{u} (Fin 3) => t i.down) (fun i => ?_) (fun σ => ?_) hsurj
    · rw [← hα i.down, pullbackCoordSection_eq, pullbackCoordSection_eq,
        ← pullbackSectionTop_comp φ g (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse 2)
          (Stacks.TwistPullbackPinned.coordGlobalSection 2 i.down)]
      exact congrArg (fun y => (Scheme.Modules.Hom.app α ⊤) y)
        (Scheme.Modules.hom_app_inv_app ((Scheme.Modules.pullbackComp φ g).app
          (Stacks.AmpleProjectiveImmersion.twistingSheafAtUniverse 2)) (op ⊤) _)
    · exact Submodule.span_mono
        (by rintro _ ⟨i, rfl⟩; exact ⟨ULift.up i, rfl⟩) (b.mem_span σ)
  let := hclosed
  let pc := Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison k 2
  have hbase : pc.iso.hom ≫ projToSpecCoeff k 2 =
      Stacks.Tag01VT.projectiveSpaceHom 2 (Spec (.of k)) := pc.toBase
  refine ⟨φ ≫ pc.iso.hom, inferInstance, ?_⟩
  rw [Category.assoc, hbase]
  exact hφ

/-- On an actual genus-nine curve the complete three-section system
must fail an actual length-two closed-subscheme separation test. -/
theorem not_surjectsOnDegreeTwo_of_genus_nine_of_h0_eq_three
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f]
    (hg : genus f = 9) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (h0 : Module.finrank k (cohomologyOverField k f L 0) = 3) :
    ¬ SurjectsOnDegreeTwo f L := by
  intro hsurj
  obtain ⟨i, hi, hif⟩ :=
    exists_planeClosedImmersion_of_surjectsOnDegreeTwo_of_h0_eq_three f L h0 hsurj
  exact M9StacksIntegration.GenusNineNotPlane.not_isClosedImmersion_of_genus_nine f hg i hif hi

end M9Native.CurvePlaneLinearSystem
