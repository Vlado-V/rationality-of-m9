module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import Mathlib.Algebra.Homology.ShortComplex.Exact

/-!
# Actual line subobjects in a nonsplit extension

For an exact extension of a line bundle by a sheaf Q, a nonzero map
from a line L to the middle sheaf cannot have degree at least that of
the quotient line when Hom(L,Q) is zero: its quotient map is a nonzero
map of equal-degree lines, hence an isomorphism, and its inverse gives
an actual splitting of the original extension.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiNonsplitLineExclusion

variable (k : Type u) [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsCurve k f] [IsProper f]

/-- The splitting is an actual right inverse of the original quotient
map; no extension-class or splitting premise is inserted. -/
theorem exists_section_of_line_degree_ge
    (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Subsingleton (L ⟶ S.X₁)]
    (j : L ⟶ S.X₂) (hj : j ≠ 0)
    (hdeg : invertibleCurveDegree k f hdim S.X₃ ≤ invertibleCurveDegree k f hdim L) :
    ∃ t : S.X₃ ⟶ S.X₂, t ≫ S.g = 𝟙 _ := by
  let : Mono S.f := hS.mono_f
  have hg : j ≫ S.g ≠ 0 := by
    intro hz
    have hl : hS.exact.lift j hz = 0 := Subsingleton.elim _ _
    have he := hS.exact.lift_f j hz
    rw [hl,zero_comp] at he
    exact hj he.symm
  have hle := invertibleCurveDegree_le_of_hom_ne_zero k f hdim L S.X₃ (j ≫ S.g) hg
  let : IsIso (j ≫ S.g) :=
    isIso_of_invertibleCurveDegree_eq_of_hom_ne_zero k f hdim L S.X₃
      (j ≫ S.g) hg (le_antisymm hle hdeg)
  exact ⟨inv (j ≫ S.g) ≫ j,by simp only [Category.assoc,IsIso.inv_hom_id]⟩

/-- In a genuinely nonsplit extension, every original nonzero line map
with no map to the kernel has strictly smaller degree than the quotient. -/
theorem line_degree_lt_of_nonsplit
    (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
    (hnonsplit : ∀ t : S.X₃ ⟶ S.X₂, t ≫ S.g ≠ 𝟙 _)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [Subsingleton (L ⟶ S.X₁)]
    (j : L ⟶ S.X₂) (hj : j ≠ 0) :
    invertibleCurveDegree k f hdim L < invertibleCurveDegree k f hdim S.X₃ := by
  by_contra hn
  obtain ⟨t,ht⟩ := exists_section_of_line_degree_ge k f hdim S hS L j hj (le_of_not_gt hn)
  exact hnonsplit t ht

end M9Native.MukaiNonsplitLineExclusion
