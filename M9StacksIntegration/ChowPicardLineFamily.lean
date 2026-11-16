module

public import M9StacksIntegration.ChowLineFamilyComparison

/-!
# Actual Picard relations give relations of the same native line caps

The native Picard group supplies genuine invertible representatives and
turns equality of classes into an actual sheaf isomorphism. Native tensor
additivity of first Chern caps therefore gives an additive map from that
actual Picard group to the original operational line-cap families.

In particular actual integer Picard relations for the moving graph lines
give the same integer linear combinations of actual Chow cap operators.
No numerical, Chern-root, K-zero, or cohomological realization is assumed.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Stacks.Chow

universe u

namespace M9Native.ChowPicardLineFamily

open ChowCapWords GradedLineCapSubring

variable {X : Scheme.{u}}

/-- The actual tensor product, with genuinely proved invertibility. -/
def tensorLine (L M : InvertibleLine X) : InvertibleLine X := by
  let := L.2
  let := M.2
  exact ⟨Scheme.Modules.tensorObj L.1 M.1, isInvertible_tensorObj L.1 M.1⟩

/-- The actual native Picard class of the actual named line. -/
def actualClass (L : InvertibleLine X) : Stacks.Picard.ofScheme X :=
  @PoincareChern.lineClass X L.1
    (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L.1 L.2)

/-- The native representative, with the native invertibility proof. -/
def representativeLine (X : Scheme.{u}) (x : Stacks.Picard.ofScheme X) : InvertibleLine X :=
  ⟨PoincareChern.lineRepresentative X x,
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry X.presheaf X.ringCatSheaf.2
      (PoincareChern.lineRepresentative X x)).1
        (PoincareChern.lineRepresentative_isInvertible X x)⟩

theorem actualClass_representative (x : Stacks.Picard.ofScheme X) :
    actualClass (representativeLine X x) = x :=
  PoincareChern.lineClass_representative X x

theorem actualClass_tensor (L M : InvertibleLine X) :
    actualClass (tensorLine L M) = actualClass L + actualClass M := by
  let := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf
    X.ringCatSheaf.2 L.1 L.2
  let := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf
    X.ringCatSheaf.2 M.1 M.2
  exact PoincareChern.lineClass_tensor L.1 M.1

variable (C : ChowSituation.{u}) (q : X ⟶ C.S) [LocallyOfFiniteType q]

/-- Native tensor additivity, on the literal original line families. -/
theorem lineFamily_tensor (L M : InvertibleLine X) :
    lineFamily C q (tensorLine L M) = lineFamily C q L + lineFamily C q M := by
  funext k i
  by_cases hi : i = 1
  · subst i
    apply AddMonoidHom.ext
    intro α
    change lineFamily C q (tensorLine L M) k 1 α =
      lineFamily C q L k 1 α + lineFamily C q M k 1 α
    rw [lineFamily_apply_one, lineFamily_apply_one, lineFamily_apply_one]
    let := L.2
    let := M.2
    exact (firstChernClassCapChow_tensorObj C q (k-1) L.1 M.1 _).symm
  · rw [lineFamily_homogeneous C q (tensorLine L M) k i hi]
    change 0 = lineFamily C q L k i + lineFamily C q M k i
    rw [lineFamily_homogeneous C q L k i hi,
      lineFamily_homogeneous C q M k i hi, zero_add]

/-- Equality in the actual native Picard group yields equality of the
same actual cap families through a genuine isomorphism. -/
theorem lineFamily_eq_of_class_eq (L M : InvertibleLine X)
    (h : actualClass L = actualClass M) : lineFamily C q L = lineFamily C q M := by
  let hL := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf
    X.ringCatSheaf.2 L.1 L.2
  let hM := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry X.presheaf
    X.ringCatSheaf.2 M.1 M.2
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff X.presheaf X.ringCatSheaf.2
    L.1 M.1 hL hM).1 h
  exact ChowLineFamilyComparison.lineFamily_congr C q L M e

def familyFunction (x : Stacks.Picard.ofScheme X) : GradedCapFamily (chowGroup C q) :=
  lineFamily C q (representativeLine X x)

theorem familyFunction_class (L : InvertibleLine X) :
    familyFunction C q (actualClass L) = lineFamily C q L :=
  lineFamily_eq_of_class_eq C q _ L (actualClass_representative (actualClass L))

/-- The genuine additive map from the native Picard group to the
original actual integral-Chow line-cap families. -/
def familyHom : Stacks.Picard.ofScheme X →+ GradedCapFamily (chowGroup C q) :=
  AddMonoidHom.mk' (familyFunction C q) fun x y => by
    let L := representativeLine X x
    let M := representativeLine X y
    have hclass : actualClass (tensorLine L M) = x+y := by
      rw [actualClass_tensor, actualClass_representative, actualClass_representative]
    have hc := familyFunction_class C q (tensorLine L M)
    rw [hclass] at hc
    exact hc.trans (lineFamily_tensor C q L M)

theorem familyHom_class (L : InvertibleLine X) :
    familyHom C q (actualClass L) = lineFamily C q L :=
  familyFunction_class C q L

/-- Every actually proved finite integer Picard relation gives the
same relation among the original operational cap families. -/
theorem lineFamily_eq_integer_combination {I : Type*} [Fintype I]
    (M : InvertibleLine X) (L : I → InvertibleLine X) (w : I → ℤ)
    (h : actualClass M = ∑ j, w j • actualClass (L j)) :
    lineFamily C q M = ∑ j, w j • lineFamily C q (L j) := by
  calc
    lineFamily C q M = familyHom C q (actualClass M) := (familyHom_class C q M).symm
    _ = familyHom C q (∑ j, w j • actualClass (L j)) := congrArg (familyHom C q) h
    _ = ∑ j, w j • lineFamily C q (L j) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [map_zsmul, familyHom_class]

end M9Native.ChowPicardLineFamily
