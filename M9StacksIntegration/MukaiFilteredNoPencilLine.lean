module

public import M9StacksIntegration.MukaiGeneratedQuotient
public import M9StacksIntegration.MukaiFilteredVanishing
public import M9StacksIntegration.MukaiNonsplitLineExclusion
public import M9StacksIntegration.MukaiPencilDegreeBounds

/-!
# No pencil line in the actual generated degree-two/degree-six extension

For the original extension in Mukai (5.2), global generation of the
middle sheaf, positive degree of the first line, and at most one of its
sections rule out a splitting: a split projection makes that line a
generated quotient, hence trivial. The genuine degree comparison then
rules out every line of degree at least six mapping to the middle
sheaf, including the equality case. With no degree-five pencil this
excludes all line subobjects with two sections.

The actual geometric construction of (5.2) is a separate input; it is
not replaced by a dimension-only bundle record here.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace M9Native.MukaiFilteredNoPencilLine

variable (k : Type u) [Field k] {X : Scheme.{u}}
variable (f : X ⟶ Spec (.of k)) [IsProper f]

/-- A genuinely generated invertible sheaf with at most one section is
trivial, and therefore its actual native degree is zero. -/
theorem degree_zero_of_epi_from_free_and_h0_le_one
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    [FiniteDimensional k (cohomologyOverField k f L 0)]
    (I : Type u) (e : SheafOfModules.free (R := X.ringCatSheaf) I ⟶ L) [Epi e]
    (hsections : Module.finrank k (cohomologyOverField k f L 0) ≤ 1) :
    invertibleCurveDegree k f hdim L = 0 := by
  obtain ⟨a,ha⟩ := MukaiGeneratedQuotient.exists_epi_from_unit_of_h0_le_one f L I e hsections
  let := ha
  let hO : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (MukaiBundle.structureModule X) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr
      (Stacks.SheafOfModules.isInvertible_unit _ _)
  let hLs : Stacks.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hL
  let : IsIso a := @Stacks.SheafOfModules.isIso_of_epi_of_isInvertible
    X.toRingedSpace (MukaiBundle.structureModule X) L a ha hO hLs
  exact invertibleCurveDegree_eq_zero_of_iso_unit k f hdim L (asIso a).symm

/-- The original generated extension has no section of its quotient
map; no nonsplitting premise is assumed. -/
theorem nonsplit_of_generated_positive_kernel
    (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
    (hpositive : 0 < invertibleCurveDegree k f hdim S.X₁)
    (hsections : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 1) :
    ∀ s : S.X₃ ⟶ S.X₂, s ≫ S.g ≠ 𝟙 _ := by
  intro s hs
  let sp := ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f
  let : Epi sp.r := epi_of_epi_fac sp.f_r
  obtain ⟨g⟩ := hgen
  have hz := degree_zero_of_epi_from_free_and_h0_le_one k f hdim S.X₁ g.I
    (g.π ≫ sp.r) hsections
  rw [hz] at hpositive
  exact (lt_irrefl 0) hpositive

variable [IsCurve k f]

/-- The equality case at the quotient degree is also excluded by
genuine nonsplitting of the original generated extension. -/
theorem hom_eq_zero_of_degree_ge_quotient
    (hdim : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
    (hpositive : 0 < invertibleCurveDegree k f hdim S.X₁)
    (hsections : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 1)
    (houter : invertibleCurveDegree k f hdim S.X₁ < invertibleCurveDegree k f hdim S.X₃)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : invertibleCurveDegree k f hdim S.X₃ ≤ invertibleCurveDegree k f hdim L)
    (j : L ⟶ S.X₂) : j = 0 := by
  have hLA : ∀ a : L ⟶ S.X₁, a = 0 :=
    MukaiFilteredVanishing.hom_eq_zero_of_degree_lt f hdim L S.X₁ (houter.trans_le hL)
  let : Subsingleton (L ⟶ S.X₁) :=
    ⟨fun a b => (hLA a).trans (hLA b).symm⟩
  by_contra hj
  have hlt := MukaiNonsplitLineExclusion.line_degree_lt_of_nonsplit k f hdim S hS
    (nonsplit_of_generated_positive_kernel k f hdim S hS hgen hpositive hsections) L j hj
  exact (not_le_of_gt hlt) hL

/-- On an actual curve without a degree-five pencil, the original
generated degree-two/degree-six extension has no line with two sections. -/
theorem hom_eq_zero_of_two_sections_of_degrees_two_six [IsAlgClosed k] [Smooth f]
    (hdim : topologicalKrullDim X ≤ 1)
    (hnp : ¬ Nonempty (LinearSeries k f hdim 5 1))
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₁]
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 S.X₃]
    [FiniteDimensional k (cohomologyOverField k f S.X₁ 0)]
    (hgen : MukaiSemiIrreducible.GloballyGenerated S.X₂)
    (hA : invertibleCurveDegree k f hdim S.X₁ = 2)
    (hB : invertibleCurveDegree k f hdim S.X₃ = 6)
    (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hL : 2 ≤ Module.finrank k (cohomologyOverField k f L 0))
    (j : L ⟶ S.X₂) : j = 0 := by
  have hsections : Module.finrank k (cohomologyOverField k f S.X₁ 0) ≤ 1 := by
    by_contra hn
    have htwo : 2 ≤ Module.finrank k (cohomologyOverField k f S.X₁ 0) := by omega
    have hd := MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp S.X₁ htwo
    rw [hA] at hd
    omega
  apply hom_eq_zero_of_degree_ge_quotient k f hdim S hS hgen
    (by rw [hA]; decide) hsections (by rw [hA,hB]; decide) L
    (by rw [hB]; exact MukaiPencilDegreeBounds.six_le_degree_of_two_sections f hdim hnp L hL) j

end M9Native.MukaiFilteredNoPencilLine
