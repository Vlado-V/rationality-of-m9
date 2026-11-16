module

public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree

/-!
# Section bounds from absence of a pencil

These statements concern the original invertible modules and their native
cohomology, rather than an abstract replacement for the curve. In particular,
absence of a degree-two pencil bounds the sections of the actual divisor
sheaf of a length-two effective Cartier divisor.

This does not yet prove separation of degree-two subschemes by the canonical
sheaf. The still-needed map comparison is Serre duality for the ideal twist,
natural with respect to its inclusion in the canonical sheaf.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace M9StacksIntegration.CanonicalPencilBounds

open CategoryTheory AlgebraicGeometry Module
open Stacks.Divisors (IsEffectiveCartierDivisor divisorSheaf)

variable {k : Type u} [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]
variable (hdim : topologicalKrullDim X ≤ 1)

/-- Two independent sections of the original invertible module give an
actual pencil of the same degree. -/
theorem nonempty_pencil_of_two_le_h0 (d : ℕ) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L = (d : ℤ))
    (h0 : 2 ≤ finrank k (cohomologyOverField k f L 0)) :
    Nonempty (LinearSeries k f hdim d 1) := by
  classical
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank
    (R := k) (M := cohomologyOverField k f L 0) (n := 2) h0
  refine ⟨{
    L := L
    isInvertible := hL
    degree_eq := hd
    V := Submodule.span k (Set.range v)
    finrank_eq := ?_ }⟩
  simp only [finrank_span_eq_card hv, Fintype.card_fin]

/-- If a curve has no pencil of degree `d`, every actual invertible module
of degree `d` has at most one independent global section. -/
theorem h0_le_one_of_no_pencil (d : ℕ)
    (hnp : ¬ Nonempty (LinearSeries k f hdim d 1)) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hd : invertibleCurveDegree k f hdim L = (d : ℤ)) :
    finrank k (cohomologyOverField k f L 0) ≤ 1 := by
  by_contra h
  exact hnp (nonempty_pencil_of_two_le_h0 f hdim d L hd (by omega))

/-- Positive genus excludes a degree-one pencil, using the native theorem
that a `g¹₁` on a curve forces its actual cohomological genus to be zero. -/
theorem no_degree_one_pencil_of_genus_ne_zero [IsCurve k f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] (hg : genus f ≠ 0) :
    ¬ Nonempty (LinearSeries k f hdim 1 1) := by
  rintro ⟨s⟩
  exact hg (genus_eq_zero_of_linearSeries_dimension_eq_degree f s rfl (by decide))

variable [IsIntegral X]

/-- For the actual divisor sheaf, the native degree is the original length
of the closed subscheme. Absence of a pencil gives the required section
bound without a supplied linear-series hypothesis. -/
theorem divisor_h0_le_one_of_no_pencil (d : ℕ)
    (hnp : ¬ Nonempty (LinearSeries k f hdim d 1))
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hD : letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      finrank k Γ(D.subscheme, ⊤) = d) :
    finrank k (cohomologyOverField k f (divisorSheaf D) 0) ≤ 1 := by
  let := Stacks.Divisors.isInvertible_divisorSheaf D
  apply h0_le_one_of_no_pencil f hdim d hnp (divisorSheaf D)
  exact (invertibleCurveDegree_divisorSheaf_eq_finrank_globalSections k f hdim D).trans
    (congrArg (fun n : ℕ => (n : ℤ)) hD)

/-- The canonical section of an effective divisor supplies the lower bound,
so the absence of a pencil makes its actual space of sections a line. -/
theorem divisor_h0_eq_one_of_no_pencil (d : ℕ)
    (hnp : ¬ Nonempty (LinearSeries k f hdim d 1))
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D]
    (hD : letI : Algebra k Γ(D.subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ (D.subschemeι ≫ f).appTop).hom.toAlgebra
      finrank k Γ(D.subscheme, ⊤) = d) :
    finrank k (cohomologyOverField k f (divisorSheaf D) 0) = 1 := by
  let := Stacks.Divisors.isInvertible_divisorSheaf D
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X (divisorSheaf D)
  let := finiteDimensional_cohomologyOverField_of_isProper k f (divisorSheaf D) 0
  let e := cohomologyOverFieldZeroIsoSections k f (divisorSheaf D)
  let s := Stacks.Divisors.divisorSheafGlobalSection D
  have hs : s ≠ 0 := divisorSheafGlobalSection_ne_zero D
  have hv : e.inv.hom s ≠ 0 := by
    intro hv
    apply hs
    exact (ConcreteCategory.bijective_of_isIso e.inv).1 (by simpa only [map_zero] using hv)
  let : Nontrivial (cohomologyOverField k f (divisorSheaf D) 0) :=
    ⟨⟨e.inv.hom s, 0, hv⟩⟩
  exact (divisor_h0_le_one_of_no_pencil f hdim d hnp D hD).antisymm
    (Nat.one_le_of_lt (Module.finrank_pos))

end M9StacksIntegration.CanonicalPencilBounds
