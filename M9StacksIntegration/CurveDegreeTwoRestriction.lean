module

public import M9StacksIntegration.CurveDivisorSections
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.DegreeTwo
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde

/-!
# The original ideal restriction tests every length-two closed subscheme

An arbitrary closed immersion is identified with the subscheme cut out
by its original kernel ideal. The isomorphism preserves the dimension
and original ground-field degree. Native cohomology and pullback-section
naturality then turn surjectivity of the original ideal restriction into
the library's full `SurjectsOnDegreeTwo` predicate.

The degree transport follows the pinned native `VeryAmpleLargeDegree`
argument, specialized to the original adjunction unit rather than a
tensor/projection-formula presentation. No reducedness or rational-point
decomposition is imposed on the test subscheme.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.CurveDegreeTwoRestriction

open CategoryTheory AlgebraicGeometry Opposite
open CurveDivisorSections

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The actual closed-immersion image has the original dimension and
the original ground-field degree. -/
theorem kernel_subscheme_dimension_degree {Z : Scheme.{u}} (r : Z ⟶ X)
    [IsClosedImmersion r] {d : ℕ} (hdeg : IsZeroDimensionalOfDegree (r ≫ f) d) :
    topologicalKrullDim r.ker.subscheme ≤ 0 ∧
      (letI : Algebra k Γ(r.ker.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (r.ker.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(r.ker.subscheme, ⊤) = d) := by
  obtain ⟨hdim, hfin⟩ := hdeg
  refine ⟨?_, ?_⟩
  · rwa [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.Hom.homeomorph r.toImage).isHomeomorph]
  · let : Algebra k Γ(r.ker.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (r.ker.subschemeι ≫ f).appTop).hom.toAlgebra
    let : Algebra k Γ(Z, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (r ≫ f).appTop).hom.toAlgebra
    have key : (Scheme.ΓSpecIso (.of k)).inv ≫ (r.ker.subschemeι ≫ f).appTop ≫
        r.toImage.appTop = (Scheme.ΓSpecIso (.of k)).inv ≫ (r ≫ f).appTop := by
      rw [← Scheme.Hom.comp_appTop, ← Category.assoc, Scheme.Hom.toImage_imageι]
    let e : Γ(r.ker.subscheme, ⊤) ≃ₐ[k] Γ(Z, ⊤) :=
      AlgEquiv.ofRingEquiv
        (f := (Scheme.Γ.mapIso (asIso r.toImage).op).commRingCatIsoToRingEquiv)
        (fun c => congrArg (fun φ => φ.hom c) key)
    exact e.toLinearEquiv.finrank_eq.trans hfin

/-- Surjectivity of the original native map on zeroth cohomology is
surjectivity of actual pullback of global sections along the divisor. -/
theorem pullbackSectionTop_surjective_of_cohomology_restriction_surjective
    (D : X.IdealSheafData) (L : X.Modules)
    (h : Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D L) 0)) :
    Function.Surjective (pullbackSectionTop D.subschemeι L) := by
  let F := (Scheme.Modules.pushforward D.subschemeι).obj
    ((Scheme.Modules.pullback D.subschemeι).obj L)
  intro σ
  obtain ⟨a, ha⟩ := h ((cohomologyOverFieldZeroEquivSections k f F).symm σ)
  refine ⟨cohomologyOverFieldZeroEquivSections k f L a, ?_⟩
  change (restrictionπ D L).app ⊤ (cohomologyOverFieldZeroEquivSections k f L a) = σ
  exact (cohomologyOverFieldZeroEquivSections_cohomologyOverFieldMap k f
    (restrictionπ D L) a).symm.trans
      ((congrArg (cohomologyOverFieldZeroEquivSections k f F) ha).trans
        ((cohomologyOverFieldZeroEquivSections k f F).apply_symm_apply σ))

/-- An actual isomorphism of the test scheme does not change
surjectivity of its original global-section restriction. -/
theorem pullbackSectionTop_comp_surjective_of_isIso
    {Y Z : Scheme.{u}} (a : Y ⟶ Z) [IsIso a] (b : Z ⟶ X) (L : X.Modules)
    (hb : Function.Surjective (pullbackSectionTop b L)) :
    Function.Surjective (pullbackSectionTop (a ≫ b) L) := by
  let : (Scheme.Modules.pullback a).Full := Functor.IsEquivalence.full
  let : (Scheme.Modules.pullback a).Faithful := Functor.IsEquivalence.faithful
  let u := (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app
    ((Scheme.Modules.pullback b).obj L)
  let : IsIso u := inferInstance
  intro σ
  obtain ⟨y, hy⟩ := SheafOfModules.iso_hom_app_surjective (asIso u) (op ⊤)
    (((Scheme.Modules.pullbackComp a b).inv.app L).val.app (op ⊤) σ)
  obtain ⟨s, rfl⟩ := hb y
  refine ⟨s, Scheme.Modules.inv_app_injective ((Scheme.Modules.pullbackComp a b).app L)
    (op ⊤) ?_⟩
  exact (pullbackSectionTop_comp a b L s).trans hy

/-- The native full degree-two predicate follows from all original
ideal-restriction tests. These are arbitrary closed subschemes. -/
theorem surjectsOnDegreeTwo_of_forall_restriction_surjective (L : X.Modules)
    (h : ∀ D : X.IdealSheafData, topologicalKrullDim D.subscheme ≤ 0 →
      (letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(D.subscheme, ⊤) = 2) →
      Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D L) 0)) :
    SurjectsOnDegreeTwo f L := by
  intro Z r hr hdeg
  let := hr
  obtain ⟨hdim, hd⟩ := kernel_subscheme_dimension_degree f r hdeg
  have hs := pullbackSectionTop_surjective_of_cohomology_restriction_surjective f r.ker L
    (h r.ker hdim hd)
  rw [← Scheme.Hom.toImage_imageι r]
  exact pullbackSectionTop_comp_surjective_of_isIso r.toImage r.ker.subschemeι L hs

end M9Native.CurveDegreeTwoRestriction
