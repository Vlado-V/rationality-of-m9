module

public import M9StacksIntegration.CurveDivisorDegree
public import M9StacksIntegration.FiniteCurveDivisor

/-!
# Degree-seven section systems on an actual nonpentagonal curve

Twisting a line bundle of degree at most seven down by an actual
length-two subscheme gives degree at most five. Absence of an actual
degree-five pencil bounds that twist's actual zeroth cohomology by one.
The original restriction exact sequence then bounds the section count
by three and forces every length-two restriction to be surjective if
there are at least three sections.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

universe u

namespace M9Native.MukaiNetDegreeBounds

open CategoryTheory AlgebraicGeometry
open CurveDivisorSections CurveDivisorDegree
open Stacks.Divisors (IsEffectiveCartierDivisor)

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f] [IsCurve k f] [Smooth f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- A length-two ideal twist of an actual line bundle of degree at most
seven has at most one section on a nonpentagonal curve. -/
theorem twistDown_h0_le_one_of_degree_le_seven_of_length_two
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L ≤ 7)
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2) :
    Module.finrank k (cohomologyOverField k f (twistDown D L) 0) ≤ 1 := by
  have htw := twistDown_degree f hdim D L
  have htwdeg : invertibleCurveDegree k f hdim (twistDown D L) ≤ 5 := by
    rw [htw, hd]
    omega
  by_contra hnot
  have hh : 2 ≤ Module.finrank k (cohomologyOverField k f (twistDown D L) 0) := by omega
  have h6 := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp (twistDown D L) hh
  omega

/-- A genuinely constructed degree-two effective divisor and its actual
restriction sequence bound all degree-at-most-seven systems by three. -/
theorem h0_le_three_of_degree_le_seven
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L ≤ 7) :
    Module.finrank k (cohomologyOverField k f L 0) ≤ 3 := by
  obtain ⟨D, hD, hOD⟩ :=
    M9StacksIntegration.LinearSeriesAddEffectiveDivisor.exists_effective_degree f hdim 2
  let := hD
  have hDdim : topologicalKrullDim D.subscheme ≤ 0 :=
    topologicalKrullDim_divisorSubscheme_le_zero hdim D
  have hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2 := by
    let : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
    have h := invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
    change invertibleCurveDegree k f hdim (Stacks.Divisors.invertibleSheaf' D) =
      (Module.finrank k Γ(D.subscheme, ⊤) : ℤ) at h
    rw [hOD] at h
    exact_mod_cast h.symm
  have hI := twistDown_h0_le_one_of_degree_le_seven_of_length_two f hdim hnp L hdeg D hd
  have hdrop := cohomology_zero_le_twistDown_add_length f D hDdim L 2 hd (by decide)
  omega

/-- No length-two test can fail for a degree-at-most-seven system with
at least three sections. The finite subscheme is proved Cartier from
the actual smooth-curve hypotheses, rather than assumed to be reduced. -/
theorem restriction_surjective_of_degree_le_seven_of_three_le_h0
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.property L]
    (hdeg : invertibleCurveDegree k f hdim L ≤ 7)
    (h0 : 3 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (D : X.IdealSheafData) (hD : topologicalKrullDim D.subscheme ≤ 0)
    (hd : letI : Algebra k Γ(D.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      Module.finrank k Γ(D.subscheme, ⊤) = 2) :
    Function.Surjective (cohomologyOverFieldMap k f (restrictionπ D L) 0) := by
  let := FiniteCurveDivisor.isEffectiveCartierDivisor_of_dimension_zero f D hD
  exact restriction_surjective_of_three_le_h0_of_twistDown_h0_le_one f D hD L hd h0
    (twistDown_h0_le_one_of_degree_le_seven_of_length_two f hdim hnp L hdeg D hd)

end M9Native.MukaiNetDegreeBounds
