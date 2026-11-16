module

public import M9StacksIntegration.StandaloneModuliDraft
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper

/-!
# The original all-test curve condition and actual cohomology

The H1 identification, proper-cohomology finiteness proof, and cartesian
preservation proof are isolated from the staged CoarseSiteComparison source.
This leaf imports only their actual ready providers, without importing the
unbuilt smooth-curve stack or a classification/coarse-space assumption.
The original standalone definitions and their all-field-point quantifiers
are used literally. All structural morphisms and coefficient actions remain
those of the original pullback square.
-/

@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace M9StacksIntegration.StandaloneCurveCohomology

universe u

section Field
variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The standalone H1 and the native genus H1 are the same derived module,
including the scalar action of the original structural morphism. -/
theorem standalone_H1_eq :
    M9StandaloneDraft.H1 f = structureSheafCohomology f 1 := rfl

theorem finite_standalone_H1 [IsProper f] :
    Module.Finite k (M9StandaloneDraft.H1 f) := by
  letI := Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  letI := finiteDimensional_cohomologyOverField_of_isProper k f
    (SheafOfModules.unit X.ringCatSheaf) 1
  exact LinearEquiv.finiteDimensional
    (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.symm

/-- The native genus uses exactly the original derived H1 module. -/
theorem genus_eq_finrank_H1 :
    genus f = Module.finrank k (M9StandaloneDraft.H1 f) := rfl

end Field

/-- Actual extension-of-scalars pullbacks preserve the original H1 dimension. -/
theorem finrank_H1_fieldBaseChange
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    {X X' : Scheme.{u}} (a : X' ⟶ X) (f' : X' ⟶ Spec (.of L))
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (h : IsPullback a f' f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :
    Module.finrank L (M9StandaloneDraft.H1 f') =
      Module.finrank k (M9StandaloneDraft.H1 f) :=
  genus_baseChange k L a f' f h

/-- The standalone scheme predicate is preserved by an actual cartesian square.
Its all-field-point genus condition is transported by the actual fibre
isomorphism, with the same field and structural scalar action. -/
theorem schemeCurve_of_isPullback
    {Z Z' T T' : Scheme.{u}} (q : Z ⟶ T) (q' : Z' ⟶ T')
    (a : Z' ⟶ Z) (b : T' ⟶ T) (hcart : IsPullback a q' q b) {g : ℕ}
    (hq : M9StandaloneDraft.SchemeCurve q g) : M9StandaloneDraft.SchemeCurve q' g := by
  letI : IsProper q := hq.1
  letI : SmoothOfRelativeDimension 1 q := hq.2.1
  letI : GeometricallyConnected q := hq.2.2.1
  letI : IsProper q' := MorphismProperty.of_isPullback (P := @IsProper) hcart hq.1
  letI : SmoothOfRelativeDimension 1 q' :=
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension 1) hcart hq.2.1
  letI : GeometricallyConnected q' :=
    MorphismProperty.of_isPullback (P := @GeometricallyConnected) hcart hq.2.2.1
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  intro L _ s
  have houter := (IsPullback.of_hasPullback q' s).paste_horiz hcart
  let e := houter.isoPullback
  have he : e.hom ≫ pullback.snd q (s ≫ b) = pullback.snd q' s :=
    houter.isoPullback_hom_snd
  have hecart : IsPullback e.hom (pullback.snd q' s) (pullback.snd q (s ≫ b))
      (Spec.map (CommRingCat.ofHom (algebraMap L L))) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
    exact IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩
  refine ⟨finite_standalone_H1 (pullback.snd q' s), ?_⟩
  change genus (pullback.snd q' s) = g
  exact (genus_baseChange L L e.hom _ _ hecart).trans (hq.2.2.2 L (s ≫ b)).2


/-- An isomorphism over the same original base preserves the entire scheme
curve condition, including the genus over every field-valued point. -/
theorem schemeCurve_of_iso
    {Z Z' T : Scheme.{u}} (q : Z ⟶ T) (q' : Z' ⟶ T)
    (e : Z' ≅ Z) (he : e.hom ≫ q = q') {g : ℕ}
    (hq : M9StandaloneDraft.SchemeCurve q g) :
    M9StandaloneDraft.SchemeCurve q' g :=
  schemeCurve_of_isPullback q q' e.hom (𝟙 T)
    (IsPullback.of_horiz_isIso ⟨by simpa only [Category.comp_id] using he⟩) hq

end M9StacksIntegration.StandaloneCurveCohomology
