/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import M9StacksIntegration.GenusNineTricanonicalEmbedding
public import M9StacksIntegration.FiniteEquationEmbedding
public import M9StacksIntegration.EquationParameterGeometry
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.Equations
public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.IdealSheafRegularity
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.UniversalFormsStrataImmersion

/-! Uniform equations and genuine finite flat models of genus-nine curves.

The regularity bound is applied to the actual P³⁹ tricanonical embedding,
whose degree and Euler characteristic have already been computed. No
condition on pencils is used. The flat models retain their literal maps
to the universal form family, so their projective polarizations can be
pulled back in the subsequent relative-Hom construction.

The proof of `exists_flat_models_embedded` is a thin replay of the native proof of
`Stacks.UniversalForms.exists_flat_families_of_forms_isImmersion` from
`ProjectiveSpace/UniversalFormsStrataImmersion.lean`, pinned at Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. It exposes the original stratum
maps and the literal pullback total spaces rather than hiding them under
existentially chosen schemes. Its Apache 2.0 source notice is retained.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.UniversalForms
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
universe u
namespace M9Native.GenusNineFiniteEquationFamilies
attribute [local instance] MvPolynomial.gradedAlgebra

abbrev equationCount (m : ℕ) : ℕ := (40 + m - 1).choose m
abbrev coefficientRing (m : ℕ) : Type u := CoeffRing.{u} 39 (equationCount m) m
abbrev universalProjection (m : ℕ) := univToBase.{u} 39 (equationCount m) m
abbrev universalEmbedding (m : ℕ) :=
  FiniteEquationEmbedding.universalEmbedding.{u} 39 (equationCount m) m
abbrev modelLine (m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (coefficientRing.{u} m))) :=
  FiniteEquationEmbedding.modelLine.{u} 39 (equationCount m) m j

theorem exists_uniform_form_degree_embedded :
    ∃ m : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (_ : genus f = 9),
      ∃ (s : Fin (equationCount m) → MvPolynomial (Fin 40) k)
        (hs : ∀ j, (s j).IsHomogeneous m)
        (e : X ≅ AlgebraicGeometry.Proj (formsGrading k s hs)),
        e.hom ≫ formsToSpec k s hs = f ∧
        IsClosedImmersion (e.hom ≫ FiniteEquationEmbedding.formsEmbedding k s hs) ∧
        Nonempty ((Scheme.Modules.pullback
          (e.hom ≫ FiniteEquationEmbedding.formsEmbedding k s hs)).obj
          (twistOver 39 (Spec (.of k)) 1) ≅
            GenusNineTricanonicalCohomology.tricanonical f) := by
  obtain ⟨m, hm⟩ := exists_isMRegular_kernel_closedImmersionQuotient.{u} 39 48 (-8)
  refine ⟨m, fun k _ _ X f _ _ _ _ hg => ?_⟩
  obtain ⟨φ, hφci, hφ, ⟨eL⟩⟩ :=
    GenusNineTricanonicalEmbedding.exists_tricanonical_closedImmersion f hg
  let := hφci
  have hφ' : φ ≫ (projectiveSpaceOverRing 39 (.of k) ↘ Spec (.of k)) = f := hφ
  have hdim := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdeg : invertibleCurveDegree k
      (φ ≫ (projectiveSpaceOverRing 39 (.of k) ↘ Spec (.of k))) hdim
      ((Scheme.Modules.pullback φ).obj (twistOver 39 (Spec (.of k)) 1)) = 48 := by
    simpa only [hφ'] using (invertibleCurveDegree_eq_of_iso k f hdim eL).trans
      (GenusNineTricanonicalCohomology.tricanonical_degree f hdim hg)
  have hχ := eulerCharacteristic_unit_eq_one_sub_genus k f hdim
  change (∑ᶠ i : ℕ, (-1 : ℤ)^i *
    (Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i) : ℤ)) =
      1 - (genus f : ℤ) at hχ
  have hχ' : (∑ᶠ i : ℕ, (-1 : ℤ)^i *
      (Module.finrank k (cohomologyOverField k
        (φ ≫ (projectiveSpaceOverRing 39 (.of k) ↘ Spec (.of k)))
        (SheafOfModules.unit X.ringCatSheaf) i) : ℤ)) = -8 := by
    have hcoh := congrArg (fun p : X ⟶ Spec (.of k) =>
      ∑ᶠ i : ℕ, (-1 : ℤ)^i *
        (Module.finrank k (cohomologyOverField k p (SheafOfModules.unit X.ringCatSheaf) i) : ℤ)) hφ'
    exact hcoh.trans (hχ.trans
      (show 1 - (genus f : ℤ) = -8 by rw [hg]; norm_num)
      )
  have hreg := hm k X φ hdim hdeg hχ'
  obtain ⟨s, hs, e, he⟩ :=
    FiniteEquationEmbedding.exists_iso_formsEmbedding_of_isMRegular φ m
    (fun d hd => hreg d (by exact_mod_cast hd))
  refine ⟨s, hs, e, ?_, ?_, ?_⟩
  · rw [← FiniteEquationEmbedding.formsEmbedding_toSpec k s hs,
      ← Category.assoc, he]
    exact hφ
  · rw [he]
    exact hφci
  · exact ⟨(Scheme.Modules.pullbackCongr he).app _ ≪≫ eL⟩

/-- The original unpolarized coverage endpoint is retained. -/
theorem exists_uniform_form_degree :
    ∃ m : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (X : Scheme.{u})
      (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
      [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (_ : genus f = 9),
      ∃ (s : Fin (equationCount m) → MvPolynomial (Fin 40) k)
        (hs : ∀ j, (s j).IsHomogeneous m)
        (e : X ≅ AlgebraicGeometry.Proj (formsGrading k s hs)),
        e.hom ≫ formsToSpec k s hs = f := by
  obtain ⟨m, hm⟩ := exists_uniform_form_degree_embedded.{u}
  refine ⟨m, ?_⟩
  intro k _ _ X f _ _ _ _ hg
  obtain ⟨s, hs, e, he, _, _⟩ := hm k X f hg
  exact ⟨s, hs, e, he⟩

theorem exists_flat_models_embedded (m : ℕ) :
    ∃ (t : ℕ) (T : Fin t → Scheme.{u})
      (j : ∀ i, T i ⟶ Spec (.of (coefficientRing.{u} m))),
      (∀ i, IsImmersion (j i)) ∧ (∀ i, IsNoetherian (T i)) ∧
      (∀ i, Flat (pullback.snd (universalProjection.{u} m) (j i))) ∧
      (∀ i, IsProper (pullback.snd (universalProjection.{u} m) (j i))) ∧
      ∀ (K : Type u) [Field K]
        (s : Fin (equationCount m) → MvPolynomial (Fin 40) K)
        (hs : ∀ a, (s a).IsHomogeneous m),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i)
          (q : AlgebraicGeometry.Proj (formsGrading K s hs) ⟶ pullback (universalProjection.{u} m) (j i)),
          IsPullback q (formsToSpec K s hs)
            (pullback.snd (universalProjection.{u} m) (j i)) x ∧
          q ≫ pullback.fst (universalProjection.{u} m) (j i) ≫ universalEmbedding.{u} m =
            FiniteEquationEmbedding.formsEmbedding K s hs ≫
              projectiveSpaceOverMap 39 (x ≫ j i) := by
  letI : IsProper (universalProjection.{u} m) :=
    Stacks.UniversalForms.isProper_univToBase 39 (equationCount m) m
  letI : LocallyOfFiniteType (universalProjection.{u} m) :=
    (Stacks.UniversalForms.isProper_univToBase 39 (equationCount m) m).toLocallyOfFiniteType
  letI : UniversallyClosed (universalProjection.{u} m) :=
    (Stacks.UniversalForms.isProper_univToBase 39 (equationCount m) m).toUniversallyClosed
  obtain ⟨t, T, j, himm, hT, hflat, hpts⟩ :=
    exists_flat_strata_of_isNoetherian (universalProjection.{u} m)
  refine ⟨t, T, j, himm, hT, hflat, fun i => inferInstance, ?_⟩
  intro K _ s hs
  letI : Algebra (CoeffRing.{u} 39 (equationCount m) m) K := (specialize K s).toAlgebra
  have hsalg : algebraMap (CoeffRing.{u} 39 (equationCount m) m) K = specialize K s := rfl
  obtain ⟨i, x, hx⟩ := hpts K (Spec.map (CommRingCat.ofHom (specialize K s)))
  have hsq := isPullback_univToBase 39 (equationCount m) m K
  rw [hsalg, ← hx] at hsq
  have hbig := IsPullback.of_right
    (h₁₂ := pullback.fst (universalProjection.{u} m) (j i))
    (v₁₂ := pullback.snd (universalProjection.{u} m) (j i))
    (h₁₁ := pullback.lift
      (FiniteEquationEmbedding.universalBaseChangeMap 39 (equationCount m) m K)
      (baseToSpec 39 (equationCount m) m K ≫ x)
      (by rw [hsq.w]; simp only [Category.assoc]))
    (by rw [pullback.lift_fst]; exact hsq) (pullback.lift_snd _ _ _)
    (IsPullback.of_hasPullback _ _)
  have key : ∀ (s₁ : Fin (equationCount m) → MvPolynomial (Fin 40) K)
      (h₁ : ∀ a, (s₁ a).IsHomogeneous m), s₁ = s →
      (∃ q : AlgebraicGeometry.Proj (formsGrading K s₁ h₁) ⟶ pullback (universalProjection.{u} m) (j i),
        IsPullback q (formsToSpec K s₁ h₁)
          (pullback.snd (universalProjection.{u} m) (j i)) x ∧
        q ≫ pullback.fst (universalProjection.{u} m) (j i) ≫ universalEmbedding.{u} m =
          FiniteEquationEmbedding.formsEmbedding K s₁ h₁ ≫
            projectiveSpaceOverMap 39 (x ≫ j i)) →
      ∃ q : AlgebraicGeometry.Proj (formsGrading K s hs) ⟶ pullback (universalProjection.{u} m) (j i),
        IsPullback q (formsToSpec K s hs)
          (pullback.snd (universalProjection.{u} m) (j i)) x ∧
        q ≫ pullback.fst (universalProjection.{u} m) (j i) ≫ universalEmbedding.{u} m =
          FiniteEquationEmbedding.formsEmbedding K s hs ≫
            projectiveSpaceOverMap 39 (x ≫ j i) := by
    rintro s₁ h₁ rfl h
    exact h
  obtain ⟨q, hq, hqemb⟩ := key (baseForms 39 (equationCount m) m K)
    (isHomogeneous_baseForms 39 (equationCount m) m K)
    (funext fun a => map_specialize_form K s hs a) ⟨_, hbig, by
      rw [← Category.assoc, pullback.lift_fst, hx]
      exact FiniteEquationEmbedding.baseChange_formsEmbedding 39 (equationCount m) m K⟩
  exact ⟨i, x, q, hq, hqemb⟩

/-- The original unpolarized finite-model endpoint is retained. -/
theorem exists_flat_models (m : ℕ) :
    ∃ (t : ℕ) (T : Fin t → Scheme.{u})
      (j : ∀ i, T i ⟶ Spec (.of (coefficientRing.{u} m))),
      (∀ i, IsImmersion (j i)) ∧ (∀ i, IsNoetherian (T i)) ∧
      (∀ i, Flat (pullback.snd (universalProjection.{u} m) (j i))) ∧
      (∀ i, IsProper (pullback.snd (universalProjection.{u} m) (j i))) ∧
      ∀ (K : Type u) [Field K]
        (s : Fin (equationCount m) → MvPolynomial (Fin 40) K)
        (hs : ∀ a, (s a).IsHomogeneous m),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i)
          (q : AlgebraicGeometry.Proj (formsGrading K s hs) ⟶ pullback (universalProjection.{u} m) (j i)),
          IsPullback q (formsToSpec K s hs)
            (pullback.snd (universalProjection.{u} m) (j i)) x := by
  obtain ⟨t, T, j, hi, hT, hf, hp, hbd⟩ := exists_flat_models_embedded.{u} m
  refine ⟨t, T, j, hi, hT, hf, hp, ?_⟩
  intro K _ s hs
  obtain ⟨i, x, q, hq, _⟩ := hbd K s hs
  exact ⟨i, x, q, hq⟩

theorem exists_finite_curve_models_embedded :
    ∃ (m t : ℕ) (T : Fin t → Scheme.{u})
      (j : ∀ i, T i ⟶ Spec (.of (coefficientRing.{u} m))),
      (∀ i, IsImmersion (j i)) ∧ (∀ i, IsNoetherian (T i)) ∧
      (∀ i, LocallyOfFinitePresentation
        (EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) (j i))) ∧
      (∀ i, QuasiCompact
        (EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) (j i))) ∧
      (∀ i, Flat (pullback.snd (universalProjection.{u} m) (j i))) ∧
      (∀ i, IsProper (pullback.snd (universalProjection.{u} m) (j i))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
        (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i)
          (q : X ⟶ pullback (universalProjection.{u} m) (j i))
          (κ : X ⟶ projectiveSpaceOverRing 39 (.of K)),
          IsPullback q f (pullback.snd (universalProjection.{u} m) (j i)) x ∧
          IsClosedImmersion κ ∧
          κ ≫ (projectiveSpaceOverRing 39 (.of K) ↘ Spec (.of K)) = f ∧
          q ≫ pullback.fst (universalProjection.{u} m) (j i) ≫ universalEmbedding.{u} m =
            κ ≫ projectiveSpaceOverMap 39 (x ≫ j i) ∧
          Nonempty ((Scheme.Modules.pullback κ).obj (twistOver 39 (Spec (.of K)) 1) ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          Nonempty ((Scheme.Modules.pullback q).obj (modelLine.{u} m (j i)) ≅
            GenusNineTricanonicalCohomology.tricanonical f) ∧
          ∀ hdim : topologicalKrullDim X ≤ 1,
            invertibleCurveDegree K f hdim
              ((Scheme.Modules.pullback q).obj (modelLine.{u} m (j i))) = 48 := by
  obtain ⟨m, hm⟩ := exists_uniform_form_degree_embedded.{u}
  obtain ⟨t, T, j, hi, hT, hf, hp, hbd⟩ := exists_flat_models_embedded.{u} m
  refine ⟨m, t, T, j, hi, hT, ?_, ?_, hf, hp, ?_⟩
  · intro i
    let := hi i
    let := hT i
    exact (EquationParameterGeometry.projection_geometry
      (ULift.{u} ℤ) (coefficientRing.{u} m) (j i)).2.2.1
  · intro i
    let := hi i
    let := hT i
    exact (EquationParameterGeometry.projection_geometry
      (ULift.{u} ℤ) (coefficientRing.{u} m) (j i)).2.1
  · intro K _ _ X f _ _ _ _ hg
    obtain ⟨s, hs, e, he, hci, ⟨eL⟩⟩ := hm K X f hg
    obtain ⟨i, x, q, hq, hqemb⟩ := hbd K s hs
    have htriangle :
        (e.hom ≫ q) ≫ pullback.fst (universalProjection.{u} m) (j i) ≫
          universalEmbedding.{u} m =
        (e.hom ≫ FiniteEquationEmbedding.formsEmbedding K s hs) ≫
          projectiveSpaceOverMap 39 (x ≫ j i) := by
      rw [Category.assoc, hqemb, ← Category.assoc]
    let eModel := FiniteEquationEmbedding.modelLineIsoOfTriangle 39 (equationCount m) m K
      (j i) (e.hom ≫ q) (e.hom ≫ FiniteEquationEmbedding.formsEmbedding K s hs)
      (x ≫ j i) htriangle ≪≫ eL
    refine ⟨i, x, e.hom ≫ q, e.hom ≫ FiniteEquationEmbedding.formsEmbedding K s hs,
      ?_, hci, ?_, htriangle, ⟨eL⟩, ⟨eModel⟩, ?_⟩
    · have h1 : IsPullback e.hom f (formsToSpec K s hs) (𝟙 _) :=
        IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact he⟩
      simpa using h1.paste_horiz hq
    · rw [Category.assoc, FiniteEquationEmbedding.formsEmbedding_toSpec]
      exact he
    · intro hdim
      exact (invertibleCurveDegree_eq_of_iso K f hdim eModel).trans
        (GenusNineTricanonicalCohomology.tricanonical_degree f hdim hg)

/-- The original coverage theorem follows from the faithful polarized models. -/
theorem exists_finite_curve_models :
    ∃ (m t : ℕ) (T : Fin t → Scheme.{u})
      (j : ∀ i, T i ⟶ Spec (.of (coefficientRing.{u} m))),
      (∀ i, IsImmersion (j i)) ∧ (∀ i, IsNoetherian (T i)) ∧
      (∀ i, LocallyOfFinitePresentation
        (EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) (j i))) ∧
      (∀ i, QuasiCompact
        (EquationParameterGeometry.projection (ULift.{u} ℤ) (coefficientRing.{u} m) (j i))) ∧
      (∀ i, Flat (pullback.snd (universalProjection.{u} m) (j i))) ∧
      (∀ i, IsProper (pullback.snd (universalProjection.{u} m) (j i))) ∧
      ∀ (K : Type u) [Field K] [IsAlgClosed K] (X : Scheme.{u})
        (f : X ⟶ Spec (.of K)) [IsProper f] [IsCurve K f] [Smooth f]
        [IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop)] (_ : genus f = 9),
        ∃ i, ∃ (x : Spec (.of K) ⟶ T i)
          (q : X ⟶ pullback (universalProjection.{u} m) (j i)),
          IsPullback q f (pullback.snd (universalProjection.{u} m) (j i)) x := by
  obtain ⟨m, t, T, j, hi, hT, hfp, hqc, hf, hp, hbd⟩ := exists_finite_curve_models_embedded.{u}
  refine ⟨m, t, T, j, hi, hT, hfp, hqc, hf, hp, ?_⟩
  intro K _ _ X f _ _ _ _ hg
  obtain ⟨i, x, q, _, hq, _⟩ := hbd K X f hg
  exact ⟨i, x, q, hq⟩

end M9Native.GenusNineFiniteEquationFamilies
end
