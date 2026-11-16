module

public import M9StacksIntegration.AllTestLargeSiteAtlas
public import M9StacksIntegration.AllTestCoproductCartesian

/-!
# An actual single fppf lift on every original test

A locally surjective map from an original represented sheaf to a genuine
original sheaf admits a lift of each represented test after a SINGLE
surjective flat locally-finitely-presented ORIGINAL scheme map. We thin
the actual covering family by points of its original target, form the
actual scheme coproduct, and use the original sheaf condition to verify
the lifted equality. No bounded-site or cover-lifting premise is assumed.
-/

set_option autoImplicit false
@[expose] public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace M9StacksIntegration.AllTestSingleFppfLift
open AllTestSheafCoproducts AllTestCoproductCartesian
universe u
variable (K : Type u) [Field K]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An actual full-original-site atlas lift over a single actual fppf cover. -/
theorem exists_single_fppf_lift
    {F : (M9StandaloneDraft.Schemes K)ᵒᵖ ⥤ Type (u+1)}
    (hF : Presheaf.IsSheaf (topology K) F)
    (U T : M9StandaloneDraft.Schemes K)
    (a : uliftYoneda.{u+1}.obj U ⟶ F)
    (ha : Presheaf.IsLocallySurjective (topology K) a)
    (b : uliftYoneda.{u+1}.obj T ⟶ F) :
    ∃ (V : M9StandaloneDraft.Schemes K) (q : V ⟶ T) (v : V ⟶ U),
      Flat q.left ∧ LocallyOfFinitePresentation q.left ∧ Surjective q.left ∧
      uliftYoneda.{u+1}.map v ≫ a = uliftYoneda.{u+1}.map q ≫ b := by
  classical
  let : Presheaf.IsLocallySurjective (topology K) a := ha
  let : Scheme.fppfPrecoverage.HasIsos := ⟨by
    intro X Y f hf
    let : IsIso f := hf
    exact f.singleton_mem_fppfPrecoverage⟩
  let x := uliftYonedaEquiv.{u+1} b
  let S := Presheaf.imageSieve a x
  have hS : S ∈ topology K T := Presheaf.imageSieve_mem _ a x
  have hS' : Sieve.overEquiv T S ∈ Scheme.fppfTopology T.left :=
    (GrothendieckTopology.mem_over_iff _ _).mp hS
  rw [Scheme.fppfTopology, Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hS'
  obtain ⟨P, hP, hPS⟩ := hS'
  obtain ⟨E, rfl⟩ := P.exists_eq_preZeroHypercover
  have hdata := (Scheme.presieve₀_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation) E).mp
    (by simpa [Scheme.fppfPrecoverage] using hP)
  let A (i : E.I₀) : M9StandaloneDraft.Schemes K := Over.mk (E.f i ≫ T.hom)
  let q₀ (i : E.I₀) : A i ⟶ T := Over.homMk (E.f i) rfl
  have hq₀ (i : E.I₀) : S (q₀ i) :=
    (Sieve.overEquiv_iff S (E.f i)).mp (hPS _ _ ⟨i⟩)
  let v₀ (i : E.I₀) : A i ⟶ U :=
    (Presheaf.localPreimage a x (q₀ i) (hq₀ i)).down
  have hv₀ (i : E.I₀) :
      uliftYoneda.{u+1}.map (v₀ i) ≫ a = uliftYoneda.{u+1}.map (q₀ i) ≫ b := by
    apply uliftYonedaEquiv.{u+1}.injective
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    exact (Presheaf.app_localPreimage a x (q₀ i) (hq₀ i)).trans
      (uliftYonedaEquiv_naturality.{u+1} b (q₀ i).op)
  let i (t : T.left) : E.I₀ := (hdata.1 t).choose
  have hi (t : T.left) : t ∈ Set.range (E.f (i t)) := (hdata.1 t).choose_spec
  let Z (t : T.left) : M9StandaloneDraft.Schemes K := A (i t)
  let q := sumMap K Z (fun t => q₀ (i t))
  let v := sumMap K Z (fun t => v₀ (i t))
  have hqf : Flat q.left :=
    IsZariskiLocalAtSource.sigmaDesc (P := @Flat) (fun t => (hdata.2 (i t)).1)
  have hqp : LocallyOfFinitePresentation q.left :=
    IsZariskiLocalAtSource.sigmaDesc (P := @LocallyOfFinitePresentation)
      (fun t => (hdata.2 (i t)).2)
  have hqs : Surjective q.left := by
    apply Surjective.sigmaDesc_of_union_range_eq_univ
    ext t
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    exact ⟨t, hi t⟩
  let FS : Sheaf (topology K) (Type (u+1)) := ⟨F, hF⟩
  let aS : (topology K).uliftYoneda.{u+1}.obj U ⟶ FS := ⟨a⟩
  let bS : (topology K).uliftYoneda.{u+1}.obj T ⟶ FS := ⟨b⟩
  have he : (topology K).uliftYoneda.{u+1}.map v ≫ aS =
      (topology K).uliftYoneda.{u+1}.map q ≫ bS := by
    apply Cofan.IsColimit.hom_ext (largeSumRepresentableIsColimit K Z)
    intro t
    change (topology K).uliftYoneda.{u+1}.map (sumInclusion K Z t) ≫
        (topology K).uliftYoneda.{u+1}.map v ≫ aS =
      (topology K).uliftYoneda.{u+1}.map (sumInclusion K Z t) ≫
        (topology K).uliftYoneda.{u+1}.map q ≫ bS
    rw [← Category.assoc, ← Functor.map_comp, sumInclusion_sumMap,
      ← Category.assoc, ← Functor.map_comp, sumInclusion_sumMap]
    exact Sheaf.hom_ext (hv₀ (i t))
  exact ⟨sumObject K Z, q, v, hqf, hqp, hqs,
    congrArg (fun m : (topology K).uliftYoneda.{u+1}.obj (sumObject K Z) ⟶ FS => m.hom) he⟩

end M9StacksIntegration.AllTestSingleFppfLift
