module

public import M9StacksIntegration.MukaiNetDegreeBounds
public import M9StacksIntegration.CurveDegreeTwoRestriction
public import M9StacksIntegration.CurvePlaneLinearSystem

/-!
# The native genus-nine obstruction to low-degree nets

An actual degree-at-most-seven line bundle with three sections would
separate every actual length-two closed subscheme on a nonpentagonal
curve. The proved native plane-genus obstruction rules this out in
genus nine. Twisting down at a constructed point bounds degree-eight
section spaces by three, and every actual degree-eight net is complete.
Its failure of plane very ampleness then produces an actual length-two
divisor with a degree-six, two-dimensional section space.

The accompanying audit records each source-bound kernel check.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiNoDegreeSevenNet

open CategoryTheory AlgebraicGeometry
open CurveDivisorSections CurveDivisorDegree
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- The no-plane theorem excludes every actual line-bundle net of
degree at most seven on the original nonpentagonal genus-nine curve. -/
theorem h0_le_two_of_degree_le_seven (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L ≤ 7) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 2 := by
  by_contra hnot
  have hthree : 3 ≤ Module.finrank k (cohomologyOverField k f L 0) := by omega
  have h0 : Module.finrank k (cohomologyOverField k f L 0) = 3 :=
    le_antisymm (MukaiNetDegreeBounds.h0_le_three_of_degree_le_seven f hdim hnp L hdeg) hthree
  apply CurvePlaneLinearSystem.not_surjectsOnDegreeTwo_of_genus_nine_of_h0_eq_three f hg L h0
  exact CurveDegreeTwoRestriction.surjectsOnDegreeTwo_of_forall_restriction_surjective f L
    (MukaiNetDegreeBounds.restriction_surjective_of_degree_le_seven_of_three_le_h0
      f hdim hnp L hdeg hthree)

theorem no_degree_seven_net (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) :
    ¬ Nonempty (LinearSeries k f hdim 7 2) := by
  rintro ⟨E⟩
  let := E.isInvertible
  let := invertible_cohomology_zero_finite f E.L
  have h := h0_le_two_of_degree_le_seven f hdim hg hnp E.L E.degree_eq.le
  have hV := Submodule.finrank_le E.V
  rw [E.finrank_eq] at hV
  omega

/-- The same native obstruction in every degree at most seven, for the
minimal-degree generation theorem. -/
theorem no_net_of_degree_le_seven (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1)) (d : ℕ) (hd : d ≤ 7) :
    ¬ Nonempty (LinearSeries k f hdim d 2) := by
  rintro ⟨E⟩
  let := E.isInvertible
  let := invertible_cohomology_zero_finite f E.L
  have h := h0_le_two_of_degree_le_seven f hdim hg hnp E.L
    (by rw [E.degree_eq]; exact_mod_cast hd)
  have hV := Submodule.finrank_le E.V
  rw [E.finrank_eq] at hV
  omega

/-- A constructed actual point divisor drops the degree by one and
loses at most one section. Thus degree at most eight allows at most
three sections, without a general Clifford-index premise. -/
theorem h0_le_three_of_degree_le_eight (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L ≤ 8) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 3 := by
  obtain ⟨D, hD, hOD⟩ :=
    M9StacksIntegration.LinearSeriesAddEffectiveDivisor.exists_effective_degree f hdim 1
  let := hD
  have hDdim : topologicalKrullDim D.subscheme ≤ 0 :=
    topologicalKrullDim_divisorSubscheme_le_zero hdim D
  have hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 1 := by
    let : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    have h := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
    change invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at h
    rw [hOD] at h
    exact_mod_cast h.symm
  have htw := twistDown_degree f hdim D L
  have htwdeg : invertibleCurveDegree k f hdim (twistDown D L) ≤ 7 := by
    rw [htw, hd]
    omega
  have hI := h0_le_two_of_degree_le_seven f hdim hg hnp (twistDown D L) htwdeg
  have hdrop := cohomology_zero_le_twistDown_add_length f D hDdim L 1 hd (by decide)
  omega

/-- Every actual degree-eight net is a complete net on the original
nonpentagonal genus-nine curve. -/
theorem degree_eight_net_h0_eq_three_and_complete (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2) :
    Module.finrank k (cohomologyOverField k f E.L 0) = 3 ∧ E.V = ⊤ := by
  let := E.isInvertible
  let := invertible_cohomology_zero_finite f E.L
  have hbound := h0_le_three_of_degree_le_eight f hdim hg hnp E.L E.degree_eq.le
  have hV := Submodule.finrank_le E.V
  rw [E.finrank_eq] at hV
  have h0 : Module.finrank k (cohomologyOverField k f E.L 0) = 3 := by omega
  exact ⟨h0, Submodule.eq_top_of_finrank_eq (by rw [E.finrank_eq, h0])⟩

/-- The failed actual plane embedding produces an actual length-two
closed subscheme with a nonsurjective original cohomology restriction.
Its Cartier property is then derived from smoothness. -/
theorem exists_length_two_restriction_defect (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2) :
    ∃ D : X.IdealSheafData,
      topologicalKrullDim D.subscheme ≤ 0 ∧
      (letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(D.subscheme, ⊤) = 2) ∧
      ¬ Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D E.L) 0) := by
  classical
  let := E.isInvertible
  have h0 := (degree_eight_net_h0_eq_three_and_complete f hdim hg hnp E).1
  have hnot : ¬ ∀ D : X.IdealSheafData, topologicalKrullDim D.subscheme ≤ 0 →
      (letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(D.subscheme, ⊤) = 2) →
      Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D E.L) 0) := by
    intro h
    exact CurvePlaneLinearSystem.not_surjectsOnDegreeTwo_of_genus_nine_of_h0_eq_three
      f hg E.L h0
      (CurveDegreeTwoRestriction.surjectsOnDegreeTwo_of_forall_restriction_surjective f E.L h)
  push Not at hnot
  exact hnot

/-- The actual degree-eight complete net produces an actual length-two
Cartier divisor D such that its original ideal twist has degree six
and exactly two sections. Generation of that pencil is the next step. -/
theorem exists_length_two_degree_six_twist (hg : genus f = 9)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (E : LinearSeries k f hdim 8 2) :
    ∃ (D : X.IdealSheafData) (hD : IsEffectiveCartierDivisor D),
      topologicalKrullDim D.subscheme ≤ 0 ∧
      (letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra;
        Module.finrank k Γ(D.subscheme, ⊤) = 2) ∧
      (letI := hD
       letI := E.isInvertible
       invertibleCurveDegree k f hdim (twistDown D E.L) = 6 ∧
       Module.finrank k (cohomologyOverField k f (twistDown D E.L) 0) = 2) := by
  let := E.isInvertible
  have h0 := (degree_eight_net_h0_eq_three_and_complete f hdim hg hnp E).1
  obtain ⟨D, hdimD, hd, hfail⟩ := exists_length_two_restriction_defect f hdim hg hnp E
  let hD := FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f D hdimD
  let := hD
  have hdegree : invertibleCurveDegree k f hdim (twistDown D E.L) = 6 := by
    rw [twistDown_degree f hdim D E.L, E.degree_eq, hd]
    norm_num
  have hlow := two_le_twistDown_h0_of_restriction_not_surjective f D hdimD E.L hd h0 hfail
  have hupp := h0_le_two_of_degree_le_seven f hdim hg hnp (twistDown D E.L)
    (by rw [hdegree]; decide)
  exact ⟨D, hD, hdimD, hd, hdegree, le_antisymm hupp hlow⟩

end M9Native.MukaiNoDegreeSevenNet
