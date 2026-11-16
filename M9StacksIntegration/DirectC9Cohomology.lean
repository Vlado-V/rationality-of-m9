module

public import M9StacksIntegration.DirectC9FamilyDegree
public import M9StacksIntegration.DirectC9FibreGeometry

/-!
# Actual H0 and H1 of the direct ninth-power family

The residue-field fibres are the actual base changes of the original
curve. Their actual degrees were computed from finite-flat divisors.
Native large-degree vanishing and Riemann--Roch therefore compute their
actual cohomology. The degree-ten twist has H0 rank ten, and the nine
moving stages have H0 ranks nine through eighteen.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 10000

attribute [local implicit_reducible] AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.CurvePower

universe u

namespace M9Native.DirectC9Cohomology

open DirectC9PoincareFamily
open DirectC9FamilyDegree (familySpace familyProjection familyClass)
open PoincareChern (lineClass)

variable (k : Type u) [Field k] [IsAlgClosed k] (C : Over (Spec (.of k)))
  [IsCurve k C.hom] [IsProper C.hom] [Smooth C.hom]

local instance original_relativeDimension : SmoothOfRelativeDimension 1 C.hom :=
  DirectC9FibreGeometry.original_relativeDimension k C

/-- The actual twist by `q+1` copies of the actual fixed section. -/
abbrev twistedLine (c₀ : power C 0 ⟶ C) (q : ℕ) : (familySpace C).Modules :=
  Scheme.Modules.tensorObj (degreeEightLine C c₀) (fixedLine C c₀ q)

instance twistedLine_isInvertible (c₀ : power C 0 ⟶ C) (q : ℕ) :
    Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (twistedLine k C c₀ q) := by
  let L : (familySpace C).Modules := degreeEightLine C c₀
  let M : (familySpace C).Modules := fixedLine C c₀ q
  letI : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L := degreeEightLine_isInvertible C c₀
  letI : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 M := fixedLine_isInvertible C c₀ q
  exact @PoincareChern.lineTensor_isInvertible (familySpace C) L M inferInstance inferInstance

theorem twistedLine_class (c₀ : power C 0 ⟶ C) (q : ℕ) :
    @lineClass (familySpace C) (twistedLine k C c₀ q) (twistedLine_isInvertible k C c₀ q) =
      @lineClass (familySpace C) (degreeEightLine C c₀) (degreeEightLine_isInvertible C c₀) +
      familyClass C (constantFamily C c₀ q) := by
  let L : (familySpace C).Modules := degreeEightLine C c₀
  let M : (familySpace C).Modules := fixedLine C c₀ q
  letI hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L := degreeEightLine_isInvertible C c₀
  letI hM : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 M := fixedLine_isInvertible C c₀ q
  exact @PoincareChern.lineClass_tensor (familySpace C) L M hL hM

theorem twistedLine_degree (c₀ : power C 0 ⟶ C) (q : ℕ) (t : (power C 9).left) :
    relativeInvertibleDegreeHomAt (familyProjection C)
      (DirectC9FibreGeometry.fibre_dimension_le_one k C) t
      (@lineClass (familySpace C) (twistedLine k C c₀ q) (twistedLine_isInvertible k C c₀ q)) =
        8 + ((q + 1 : ℕ) : ℤ) := by
  rw [twistedLine_class,map_add,DirectC9FamilyDegree.degreeEightLine_degree,
    DirectC9FamilyDegree.constantFamily_degree]
  simp only [Nat.cast_add,Nat.cast_one]

/-- The relative Picard degree is the actual degree of the actual
pulled-back line on this actual residue-field fibre. -/
theorem fibreLine_degree (L : (familySpace C).Modules)
    [hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L] (t : (power C 9).left) :
    let π := familyProjection C
    let Lf := (Scheme.Modules.pullback (π.fiberι t)).obj L
    let hLf := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (π.fiberι t) L
    let hLfA := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hLf
    @invertibleCurveDegree ((power C 9).left.residueField t) _ (π.fiber t)
      (π.fiberToSpecResidueField t) _
      (DirectC9FibreGeometry.fibre_dimension_le_one k C t) Lf hLfA =
      relativeInvertibleDegreeHomAt π (DirectC9FibreGeometry.fibre_dimension_le_one k C) t
        (@lineClass (familySpace C) L hL) := by
  let π := familyProjection C
  letI hLf := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (π.fiberι t) L
  have heq := @PoincareChern.lineClass_pullback (π.fiber t) (familySpace C) (π.fiberι t) L hL
  have h := congrArg (invertibleCurveDegreeHom ((power C 9).left.residueField t)
    (π.fiberToSpecResidueField t) (DirectC9FibreGeometry.fibre_dimension_le_one k C t)) heq
  rw [invertibleCurveDegreeHom_picardClass] at h
  exact h

/-- Actual H1 vanishing and actual H0 rank on every actual fibre. -/
theorem largeDegree_fibreH0H1 (L : (familySpace C).Modules)
    [hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L]
    (hg : genus C.hom = 9) (r : ℕ) (hr : 9 ≤ r)
    (hd : ∀ t : (power C 9).left,
      relativeInvertibleDegreeHomAt (familyProjection C)
        (DirectC9FibreGeometry.fibre_dimension_le_one k C) t (@lineClass (familySpace C) L hL) =
          (r : ℤ) + 8) (t : (power C 9).left) :
    IsZero (cohomologyOverField ((power C 9).left.residueField t)
      ((familyProjection C).fiberToSpecResidueField t)
      ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj L) 1) ∧
    Module.finrank ((power C 9).left.residueField t)
      (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj L) 0) = r := by
  let π := familyProjection C
  letI := DirectC9FibreGeometry.residueAlgebra k C t
  let Lf := (Scheme.Modules.pullback (π.fiberι t)).obj L
  letI hLf := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (π.fiberι t) L
  have hLfA := (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hLf
  have hd' : @invertibleCurveDegree ((power C 9).left.residueField t) _ (π.fiber t)
      (π.fiberToSpecResidueField t) _
      (IsCurve.topologicalKrullDim_eq_one (k := ((power C 9).left.residueField t))
        (f := π.fiberToSpecResidueField t)).le Lf hLfA = (r : ℤ) + 8 :=
    (fibreLine_degree k C L t).trans (hd t)
  exact PoincareChern.LargeDegreeField.genusNine_h0_h1 k ((power C 9).left.residueField t)
    C.hom (π.fiberι t ≫ (CartesianMonoidalCategory.fst C (power C 9)).left) (π.fiberToSpecResidueField t)
    (DirectC9FibreGeometry.fibre_isPullback_original k C t) Lf hLfA hg r hr hd'

theorem partialLine_fibreH0H1 (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (j : ℕ) (hj : j ≤ 9) (t : (power C 9).left) :
    IsZero (cohomologyOverField ((power C 9).left.residueField t)
      ((familyProjection C).fiberToSpecResidueField t)
      ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj (partialLine C c₀ j hj)) 1) ∧
    Module.finrank ((power C 9).left.residueField t)
      (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj (partialLine C c₀ j hj)) 0) = 9 + j := by
  letI : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 (partialLine C c₀ j hj) :=
    partialLine_isInvertible C c₀ j hj
  refine largeDegree_fibreH0H1 k C (partialLine C c₀ j hj) hg (9 + j) (by omega) ?_ t
  intro u
  have hd := DirectC9FamilyDegree.partialLine_degree C c₀
    (DirectC9FibreGeometry.fibre_dimension_le_one k C) j hj u
  have he : (17 : ℤ) + j = ((9 + j : ℕ) : ℤ) + 8 := by omega
  exact hd.trans he

theorem twistedLine_fibreH0H1 (c₀ : power C 0 ⟶ C) (hg : genus C.hom = 9)
    (q : ℕ) (hq : 8 ≤ q) (t : (power C 9).left) :
    IsZero (cohomologyOverField ((power C 9).left.residueField t)
      ((familyProjection C).fiberToSpecResidueField t)
      ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj (twistedLine k C c₀ q)) 1) ∧
    Module.finrank ((power C 9).left.residueField t)
      (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj (twistedLine k C c₀ q)) 0) = q + 1 := by
  refine largeDegree_fibreH0H1 k C (twistedLine k C c₀ q) hg (q + 1) (by omega) ?_ t
  intro u
  exact (twistedLine_degree k C c₀ q u).trans (by push_cast; ring)

/-- Actual curve dimension kills every actual higher fibre cohomology group. -/
theorem fibre_cohomology_above_one_zero (L : (familySpace C).Modules)
    [hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L] (t : (power C 9).left) (n : ℕ) (hn : 1 < n) :
    IsZero (cohomologyOverField ((power C 9).left.residueField t)
      ((familyProjection C).fiberToSpecResidueField t)
      ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj L) n) := by
  let π := familyProjection C
  let Lf := (Scheme.Modules.pullback (π.fiberι t)).obj L
  letI hLf := Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj (π.fiberι t) L
  letI : SheafOfModules.IsInvertible (π.fiber t).presheaf (π.fiber t).ringCatSheaf.2 Lf :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mp hLf
  letI : Lf.IsQuasicoherent := Stacks.Divisors.isQuasicoherent_of_isInvertible Lf
  exact isZero_cohomologyOverField_of_topologicalKrullDim_le
    ((power C 9).left.residueField t) (π.fiberToSpecResidueField t) Lf (d := 1)
    (DirectC9FibreGeometry.fibre_dimension_le_one k C t) hn

/-- All actual fibre cohomology ranks, in the precise form consumed by
native cohomology-and-base-change. -/
theorem largeDegree_fibreFinrank (L : (familySpace C).Modules)
    [hL : Stacks.SheafOfModules.IsInvertible (familySpace C).presheaf
      (familySpace C).ringCatSheaf.2 L]
    (hg : genus C.hom = 9) (r : ℕ) (hr : 9 ≤ r)
    (hd : ∀ t : (power C 9).left,
      relativeInvertibleDegreeHomAt (familyProjection C)
        (DirectC9FibreGeometry.fibre_dimension_le_one k C) t (@lineClass (familySpace C) L hL) =
          (r : ℤ) + 8) (t : (power C 9).left) (n : ℕ) :
    Module.finrank ((power C 9).left.residueField t)
      (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj L) n) =
      if n = 0 then r else 0 := by
  obtain ⟨h1,h0⟩ := largeDegree_fibreH0H1 k C L hg r hr hd t
  by_cases hn0 : n = 0
  · subst n
    simpa only [ite_true] using h0
  · rw [ite_eq_right hn0]
    have hz : IsZero (cohomologyOverField ((power C 9).left.residueField t)
        ((familyProjection C).fiberToSpecResidueField t)
        ((Scheme.Modules.pullback ((familyProjection C).fiberι t)).obj L) n) := by
      by_cases hn1 : n = 1
      · simpa only [hn1] using h1
      · exact fibre_cohomology_above_one_zero k C L t n (by omega)
    haveI := ModuleCat.subsingleton_of_isZero hz
    exact Module.finrank_zero_of_subsingleton

end M9Native.DirectC9Cohomology
