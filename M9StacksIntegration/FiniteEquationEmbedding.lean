/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Curves.StableCurveEquations.Equations
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleAffineBase.Basic
public import StacksFrontier.AlgebraicGeometry.ProjClosedImmersion.Basic

/-! Finite equations with the original projective embedding retained.

The regularity argument is a thin replay of the proof in native
`Curves/StableCurveEquations/Equations.lean`, pinned at Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b. Its output here retains the
actual ambient projective-space triangle. Pulling back the literal
hyperplane line along this triangle therefore requires no assertion
that an arbitrary curve isomorphism preserves a polarization.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.UniversalForms
open Stacks.RingTheory.HomogeneousQuotient
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
universe u
namespace M9Native.FiniteEquationEmbedding
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual quotient immersion, read in the native projective-space model. -/
def formsEmbedding {n M m : ℕ} (K : Type u) [CommRing K]
    (s : Fin M → MvPolynomial (Fin (n + 1)) K)
    (hs : ∀ j, (s j).IsHomogeneous m) :
    AlgebraicGeometry.Proj (formsGrading K s hs) ⟶ projectiveSpaceOverRing n (.of K) :=
  Proj.map (quotientMk (polyGrading K n) (formsIdeal K s hs))
    (Stacks.ProjQuotientChartIdeal.irrelevant_le_map_quotientMk
      (polyGrading K n) (formsIdeal K s hs)) ≫
    (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso K n).inv

instance formsEmbedding_isClosedImmersion {n M m : ℕ} (K : Type u) [CommRing K]
    (s : Fin M → MvPolynomial (Fin (n + 1)) K)
    (hs : ∀ j, (s j).IsHomogeneous m) : IsClosedImmersion (formsEmbedding K s hs) := by
  letI := Proj.isClosedImmersion_map_of_surjective
    (Stacks.ProjQuotientChartIdeal.irrelevant_le_map_quotientMk
      (polyGrading K n) (formsIdeal K s hs)) Ideal.Quotient.mk_surjective
  dsimp only [formsEmbedding]
  infer_instance

/-- The quotient immersion has its literal original field structure map. -/
theorem formsEmbedding_toSpec {n M m : ℕ} (K : Type u) [CommRing K]
    (s : Fin M → MvPolynomial (Fin (n + 1)) K)
    (hs : ∀ j, (s j).IsHomogeneous m) :
    formsEmbedding K s hs ≫ (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) =
      formsToSpec K s hs := by
  have hcmp : (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso K n).inv ≫
        (projectiveSpaceOverRing n (.of K) ↘ Spec (.of K)) =
      Proj.toSpecZero (polyGrading K n) ≫
        Spec.map (CommRingCat.ofHom ((GradedRing.projZeroRingHom' (polyGrading K n)).comp
          (algebraMap K (MvPolynomial (Fin (n + 1)) K)))) := by
    rw [Iso.inv_comp_eq]
    exact (Stacks.AlgebraicGeometry.ProjBaseChange.polynomialComparison K n).toBase.symm
  rw [formsEmbedding, Category.assoc, hcmp, Proj.map_toSpecZero_assoc, ← Spec.map_comp]
  congr 2
  ext c
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
    GradedRingHom.gradedZeroRingHom_apply_coe, SetLike.GradeZero.coe_algebraMap,
    GradedRing.coe_projZeroRingHom'_apply, GradedRing.projZeroRingHom_apply,
    DirectSum.decompose_of_mem_same (polyGrading K n)
      (SetLike.algebraMap_mem_graded (polyGrading K n) c)]
  rfl

/-- The original universal quotient immersion into projective space over
the coefficient ring. -/
abbrev universalEmbedding (n M m : ℕ) :=
  formsEmbedding (CoeffRing.{u} n M m) (form n M m) (isHomogeneous_form n M m)

/-- The genuine universal hyperplane polarization. -/
abbrev universalLine (n M m : ℕ) :=
  (Scheme.Modules.pullback (universalEmbedding.{u} n M m)).obj
    (twistOver n (Spec (.of (CoeffRing.{u} n M m))) 1)

/-- Its literal pullback to a flat model over a coefficient stratum. -/
abbrev modelLine (n M m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (CoeffRing.{u} n M m))) :
    (pullback (univToBase.{u} n M m) j).Modules :=
  (Scheme.Modules.pullback (pullback.fst (univToBase.{u} n M m) j)).obj
    (universalLine.{u} n M m)

instance universalLine_isInvertible (n M m : ℕ) :
    Stacks.Ample.IsInvertibleModule _ (universalLine.{u} n M m) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback (universalEmbedding.{u} n M m) _

instance modelLine_isInvertible (n M m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (CoeffRing.{u} n M m))) :
    Stacks.Ample.IsInvertibleModule (pullback (univToBase.{u} n M m) j)
      (modelLine.{u} n M m j) :=
  Stacks.InvertiblePullback.isInvertibleModule_pullback
    (pullback.fst (univToBase.{u} n M m) j) (universalLine.{u} n M m)

/-- The literal universal O(1) is relatively ample for the original
universal projection, by its actual quotient closed immersion. -/
theorem universalLine_isRelativelyAmple (n M m : ℕ) :
    Stacks.RelativeAmple.IsRelativelyAmple (univToBase.{u} n M m)
      (universalLine.{u} n M m) := by
  apply (Stacks.RelativeAmpleAffineBase.isRelativelyAmple_iff_isAmple _ _).mpr
  exact Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom
    (universalEmbedding.{u} n M m) _
    (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n _)

/-- Every literal stratum model inherits actual relative ampleness by
the native cartesian base-change theorem. -/
theorem modelLine_isRelativelyAmple (n M m : ℕ) {T : Scheme.{u}}
    (j : T ⟶ Spec (.of (CoeffRing.{u} n M m))) :
    Stacks.RelativeAmple.IsRelativelyAmple (pullback.snd (univToBase.{u} n M m) j)
      (modelLine.{u} n M m j) :=
  Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
    (IsPullback.of_hasPullback _ _) _ (universalLine_isRelativelyAmple n M m)

/-- Read the original top morphism from a native cartesian square. -/
abbrev pullbackTop {X Y Z S : Scheme.{u}} {f : X ⟶ Y} {g : X ⟶ Z}
    {h : Y ⟶ S} {i : Z ⟶ S} (_ : IsPullback f g h i) := f

/-- The literal native base-change map, retained from its original
cartesian square without reconstructing the coefficient quotient. -/
abbrev universalBaseChangeMap (n M m : ℕ) (K : Type u) [CommRing K]
    [Algebra (CoeffRing.{u} n M m) K] :=
  pullbackTop (isPullback_univToBase n M m K)

/-- The actual quotient base-change map preserves all ambient coordinates. -/
theorem baseChange_formsEmbedding (n M m : ℕ) (K : Type u) [CommRing K]
    [Algebra (CoeffRing.{u} n M m) K] :
    universalBaseChangeMap n M m K ≫
      universalEmbedding.{u} n M m =
    formsEmbedding K (baseForms n M m K) (isHomogeneous_baseForms n M m K) ≫
      projectiveSpaceOverRingMap n
        (CommRingCat.ofHom (algebraMap (CoeffRing.{u} n M m) K)) := by
  letI : CommRing (UnivQuot.{u} n M m) :=
    @Ideal.Quotient.commRing (MvPolynomial (Fin (n + 1)) (CoeffRing.{u} n M m))
      inferInstance (ideal.{u} n M m).toIdeal
  have hring :
      (baseChangeGradedRingHom n M m K).comp
        (quotientMk (polyGrading (CoeffRing.{u} n M m) n) (ideal n M m)) =
      (quotientMk (polyGrading K n) (baseIdeal n M m K)).comp
        (Stacks.ProjectiveCohomology.polyGradedMap (Fin (n + 1))
          (algebraMap (CoeffRing.{u} n M m) K)) := by
    apply GradedRingHom.ext
    intro p
    change tensorGradedAlgHom n M m K
      ((1 : K) ⊗ₜ[CoeffRing.{u} n M m] univMk n M m p) =
        baseMk n M m K (MvPolynomial.map (algebraMap (CoeffRing.{u} n M m) K) p)
    rw [tensorGradedAlgHom_tmul, one_smul, baseChangeAlgHom_univMk]
  have hproj :
      universalBaseChangeMap n M m K ≫
        universalEmbedding.{u} n M m ≫
          (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso (CoeffRing.{u} n M m) n).hom =
      formsEmbedding K (baseForms n M m K) (isHomogeneous_baseForms n M m K) ≫
        (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso K n).hom ≫
        Stacks.ProjectiveCohomology.projModelMap n
          (algebraMap (CoeffRing.{u} n M m) K) := by
    simp only [universalEmbedding, formsEmbedding, Category.assoc, Iso.inv_hom_id_assoc,
      Iso.inv_hom_id, Category.comp_id]
    rw [universalBaseChangeMap, pullbackTop,
      Stacks.ProjectiveCohomology.projModelMap, ← Proj.map_comp, ← Proj.map_comp]
    exact Stacks.ProjectiveCohomology.Proj_map_congr _ _ _ _ hring
  calc
    _ = (universalBaseChangeMap n M m K ≫ universalEmbedding.{u} n M m ≫
        (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso (CoeffRing.{u} n M m) n).hom) ≫
        (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso (CoeffRing.{u} n M m) n).inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
    _ = _ := congrArg (fun g => g ≫
      (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso (CoeffRing.{u} n M m) n).inv) hproj
    _ = _ := by
      rw [Category.assoc, Category.assoc,
        Stacks.ProjectiveCohomology.projModelMap_comp_polynomialComparison_iso_inv,
        Iso.hom_inv_id_assoc]

/-- Pullback of literal universal O(1) along the actual base-change map
is the literal hyperplane pullback for the prescribed equations. -/
def baseChangeLineIso (n M m : ℕ) (K : Type u) [CommRing K]
    [Algebra (CoeffRing.{u} n M m) K] :
    (Scheme.Modules.pullback (universalBaseChangeMap n M m K)).obj
        (universalLine.{u} n M m) ≅
      (Scheme.Modules.pullback (formsEmbedding K (baseForms n M m K)
        (isHomogeneous_baseForms n M m K))).obj (twistOver n (Spec (.of K)) 1) :=
  (Scheme.Modules.pullbackComp _ (universalEmbedding.{u} n M m)).app _ ≪≫
    (Scheme.Modules.pullbackCongr (baseChange_formsEmbedding n M m K)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ (projectiveSpaceOverRingMap n
      (CommRingCat.ofHom (algebraMap (CoeffRing.{u} n M m) K)))).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso n
        (Spec.map (CommRingCat.ofHom (algebraMap (CoeffRing.{u} n M m) K))) 1)

/-- An actual ambient triangle transports the original model's
hyperplane line to the native hyperplane pullback over the test field. -/
def modelLineIsoOfTriangle (n M m : ℕ) (K : Type u) [CommRing K]
    {T Z : Scheme.{u}} (j : T ⟶ Spec (.of (CoeffRing.{u} n M m)))
    (q : Z ⟶ pullback (univToBase.{u} n M m) j)
    (κ : Z ⟶ projectiveSpaceOverRing n (.of K))
    (g : Spec (.of K) ⟶ Spec (.of (CoeffRing.{u} n M m)))
    (h : q ≫ pullback.fst (univToBase.{u} n M m) j ≫ universalEmbedding.{u} n M m =
      κ ≫ projectiveSpaceOverMap n g) :
    (Scheme.Modules.pullback q).obj (modelLine.{u} n M m j) ≅
      (Scheme.Modules.pullback κ).obj (twistOver n (Spec (.of K)) 1) :=
  (Scheme.Modules.pullback q).mapIso
      ((Scheme.Modules.pullbackComp (pullback.fst (univToBase.{u} n M m) j)
        (universalEmbedding.{u} n M m)).app _) ≪≫
    (Scheme.Modules.pullbackComp q
      (pullback.fst (univToBase.{u} n M m) j ≫ universalEmbedding.{u} n M m)).app _ ≪≫
    (Scheme.Modules.pullbackCongr h).app _ ≪≫
    ((Scheme.Modules.pullbackComp κ (projectiveSpaceOverMap n g)).app _).symm ≪≫
    (Scheme.Modules.pullback κ).mapIso
      (Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.twistOverPullbackIso n g 1)

variable {k : Type u} [Field k] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ projectiveSpaceOverRing n (.of k)) [IsClosedImmersion φ]

private theorem exists_fin_isHomogeneous_span_eq (m : ℕ)
    {T : Set (MvPolynomial (Fin (n + 1)) k)}
    (hT : T ⊆ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m) :
    ∃ s : Fin ((n + 1 + m - 1).choose m) → MvPolynomial (Fin (n + 1)) k,
      (∀ j, (s j).IsHomogeneous m) ∧ Ideal.span (Set.range s) = Ideal.span T := by
  classical
  let V := Submodule.span k T
  have hVle : V ≤ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m := Submodule.span_le.2 hT
  have hSm : Module.finrank k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m) =
      (n + 1 + m - 1).choose m := by
    rw [MvPolynomial.finrank_homogeneousSubmodule, Fintype.card_fin]
  have : Module.Finite k (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k m) :=
    Module.finite_of_finrank_pos (hSm ▸ Nat.choose_pos (by omega))
  have : Module.Finite k V := Submodule.finiteDimensional_of_le hVle
  have hr : Module.finrank k V ≤ (n + 1 + m - 1).choose m :=
    hSm ▸ Submodule.finrank_mono hVle
  let bV := Module.finBasis k V
  let s : Fin ((n + 1 + m - 1).choose m) → MvPolynomial (Fin (n + 1)) k := fun j =>
    if h : (j : ℕ) < Module.finrank k V then (bV ⟨j, h⟩ : MvPolynomial (Fin (n + 1)) k) else 0
  have hsV : ∀ j, s j ∈ V := fun j => by
    simp only [s]
    split_ifs
    · exact (bV _).2
    · exact V.zero_mem
  refine ⟨s, fun j => hVle (hsV j), le_antisymm ?_ ?_⟩
  · refine Ideal.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact Submodule.span_subset_span k _ T (hsV j)
  · refine Ideal.span_le.2 fun b hb => ?_
    have hbV : (⟨b, Submodule.subset_span hb⟩ : V) ∈ Submodule.span k (Set.range bV) := by
      rw [bV.span_eq]
      trivial
    refine Submodule.span_le (p := ((Ideal.span (Set.range s)).restrictScalars k).comap
      V.subtype) |>.2 ?_ hbV
    rintro _ ⟨i, rfl⟩
    refine Ideal.subset_span ⟨⟨i, i.2.trans_le hr⟩, ?_⟩
    simp only [s, dite_eq_left i.2]
    rfl

/-- The regularity construction preserves the actual ambient embedding. -/
theorem exists_iso_formsEmbedding_of_isMRegular (m : ℕ)
    (hreg : ∀ d : ℕ, m ≤ d → IsMRegular k n (kernel (closedImmersionQuotient φ)) d) :
    ∃ (s : Fin ((n + 1 + m - 1).choose m) → MvPolynomial (Fin (n + 1)) k)
      (hs : ∀ j, (s j).IsHomogeneous m)
      (e : X ≅ AlgebraicGeometry.Proj (formsGrading k s hs)),
      e.hom ≫ formsEmbedding k s hs = φ := by
  classical
  let 𝒮 := polyGrading k n
  let IX := Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme 𝒮
    (projModelEmbedding φ)
  obtain ⟨s, hs, hspan⟩ := exists_fin_isHomogeneous_span_eq (T := equationsOfDegree φ m) m
    fun _ ⟨hb, _⟩ => hb
  have h_le : formsIdeal k s hs ≤ IX := by
    change Ideal.span (Set.range s) ≤ IX.toIdeal
    rw [hspan]
    exact Ideal.span_le.2 fun b ⟨hb, hb0⟩ =>
      (mem_homogeneousIdealOfClosedSubscheme_iff φ m ⟨b, hb⟩).2 hb0
  have hm : ∀ d, m ≤ d → ∀ a ∈ 𝒮 d, a ∈ IX.toIdeal →
      a ∈ (formsIdeal k s hs).toIdeal := by
    intro d hd a ha haX
    change a ∈ Ideal.span (Set.range s)
    rw [hspan]
    exact mem_span_equationsOfDegree_of_isMRegular φ m hreg d hd a
      ⟨ha, (mem_homogeneousIdealOfClosedSubscheme_iff φ d ⟨a, ha⟩).1 haX⟩
  have := isIso_projMap_quotientFactor 𝒮 h_le m hm
  obtain ⟨e₁, he₁⟩ :=
    Stacks.ClosedSubschemeProjectiveSpace.closedSubscheme_iso_projQuotient (R := k) (n := n) φ
  refine ⟨s, hs, e₁ ≪≫ asIso (Proj.map (quotientFactor 𝒮 h_le)
    (irrelevant_le_map_quotientFactor 𝒮 h_le)), ?_⟩
  have hring : (quotientFactor 𝒮 h_le).comp (quotientMk 𝒮 (formsIdeal k s hs)) =
      quotientMk 𝒮 IX := GradedRingHom.ext fun _ => rfl
  have hkey : Proj.map (quotientFactor 𝒮 h_le)
        (irrelevant_le_map_quotientFactor 𝒮 h_le) ≫ formsEmbedding k s hs =
      Stacks.ClosedSubschemeProjQuotient.ambientHom 𝒮 (projModelEmbedding φ) ≫
        (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso k n).inv := by
    rw [formsEmbedding, ← Category.assoc, ← Proj.map_comp,
      Stacks.ProjQuotientChartIdeal.ambientHom_eq_projMap]
    exact congrArg (fun g => g ≫ (Stacks.ClosedSubschemeProjectiveSpace.comparisonIso k n).inv)
      (Stacks.ProjectiveCohomology.Proj_map_congr _ _ _ _ hring)
  rw [Iso.trans_hom, asIso_hom, Category.assoc, hkey]
  exact he₁

/-- The actual embedding triangle transports any specified ambient module. -/
def originalModuleIso {M m : ℕ}
    {s : Fin M → MvPolynomial (Fin (n + 1)) k}
    {hs : ∀ j, (s j).IsHomogeneous m}
    (e : X ≅ AlgebraicGeometry.Proj (formsGrading k s hs))
    (he : e.hom ≫ formsEmbedding k s hs = φ)
    (L : (projectiveSpaceOverRing n (.of k)).Modules) :
    (Scheme.Modules.pullback e.hom).obj
        ((Scheme.Modules.pullback (formsEmbedding k s hs)).obj L) ≅
      (Scheme.Modules.pullback φ).obj L :=
  (Scheme.Modules.pullbackComp e.hom (formsEmbedding k s hs)).app L ≪≫
    (Scheme.Modules.pullbackCongr he).app L

end M9Native.FiniteEquationEmbedding
end
