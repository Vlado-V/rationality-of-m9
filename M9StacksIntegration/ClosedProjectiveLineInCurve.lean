module

public import M9StacksIntegration.QuadraticTrisecant
public import M9StacksIntegration.NonzeroSectionZeroFinite
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.ProjectiveLine
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree

/-! An actual projective line cannot lie in a positive-genus integral
curve. Dimension drop proves that its genuine closed immersion is
surjective; reducedness then makes it an isomorphism. The original
field projection and native genus cohomology are retained. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096
set_option linter.style.haveILetI false

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (projToSpecCoeff)
open M9Native.ProjectiveQuadraticCohomology

universe u

namespace M9Native.ClosedProjectiveLineInCurve

variable (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [IsCurve K f]

include f

/-- Proper closed subsets of the actual integral curve are zero-dimensional,
so a genuine closed projective line must cover the curve. -/
theorem isIso_of_closedImmersion (g : projective K 1 ⟶ X) [IsClosedImmersion g] : IsIso g := by
  have hsurj : Function.Surjective g := by
    by_contra h
    have hne : Set.range g ≠ Set.univ := fun e => h (Set.range_eq_univ.mp e)
    have hdim : topologicalKrullDim (Set.range g) ≤ 0 :=
      topologicalKrullDim_le_zero_of_isClosed_of_ne_univ
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := f)).le
        (Set.range g) g.isClosedEmbedding.isClosed_range hne
    have hsource : topologicalKrullDim (projective K 1) ≤ 0 :=
      (topologicalKrullDim_le_of_range_subset g (Set.range g) subset_rfl).trans hdim
    have hone : topologicalKrullDim (projective K 1) = 1 := by
      simpa only [Nat.reduceSub, Nat.cast_one] using
        Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K (r := 2) (by decide)
    rw [hone] at hsource
    norm_num at hsource
  letI : Surjective g := ⟨hsurj⟩
  exact isIso_of_isClosedImmersion_of_surjective g

/-- The actual original base-field genus is zero if that curve contains
a closed projective line OVER THE ORIGINAL FIELD. -/
theorem genus_eq_zero_of_closedImmersion (g : projective K 1 ⟶ X)
    [IsClosedImmersion g] (hg : g ≫ f = projToSpecCoeff K 1) : genus f = 0 := by
  letI : IsIso g := isIso_of_closedImmersion K f g
  have h : genus (g ≫ f) = genus f := by
    rw [genus_eq_finrank_structureSheafCohomology,
      genus_eq_finrank_structureSheafCohomology]
    exact (structureSheafCohomologyIsoCohomologyOverField K (g ≫ f) 1).toLinearEquiv.finrank_eq.trans
      ((finrank_cohomologyOverField_unit_pushforward K g f 1).trans
        (structureSheafCohomologyIsoCohomologyOverField K f 1).toLinearEquiv.finrank_eq.symm)
  rw [hg] at h
  exact h.symm.trans (Stacks.Curves.genus_projToSpecCoeff_one K)

/-- A genuine ambient projective line admits no factorization through
the original positive-genus curve. All closedness is actual geometry. -/
theorem no_line_factor {Y : Scheme.{u}} (q : Y ⟶ Spec (.of K))
    (i : X ⟶ Y) [IsClosedImmersion i] (hi : i ≫ q=f)
    (l : projective K 1 ⟶ Y) [IsClosedImmersion l]
    (hl : l ≫ q=projToSpecCoeff K 1) (hgenus : genus f ≠ 0) :
    ¬ ∃g:projective K 1⟶X,g≫i=l := by
  rintro ⟨g,hg⟩
  letI : IsClosedImmersion (g ≫ i) := hg.symm ▸ inferInstance
  letI : IsClosedImmersion g := IsClosedImmersion.of_comp_isClosedImmersion g i
  have hbase : g ≫ f=projToSpecCoeff K 1 := by
    rw [← hi, ← Category.assoc, hg, hl]
  exact hgenus (genus_eq_zero_of_closedImmersion K f g hbase)

end M9Native.ClosedProjectiveLineInCurve
