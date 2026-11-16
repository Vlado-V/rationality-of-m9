module

public import M9StacksIntegration.PencilDegreePullback
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.ResidueField
public import StacksFrontier.FieldTheory.Separable.Defs

/-!
# Actual generic separability of a nonconstant curve map in characteristic zero

Nonconstancy of the original proper-curve map gives actual finiteness
and dominance. Its finite fibers have closed points, so the native
residue-field theorem supplies the finite extension at the original
generic point. The literal structure map from the characteristic-zero
base field gives characteristic zero on the target residue field, and
perfectness proves separable generation of every finite-type subfield.
No generic separability, differential nonvanishing, or field degree is
supplied as a premise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

open CategoryTheory AlgebraicGeometry

universe u

namespace M9Native.CurveGenericResidueSeparable

/-- The actual residue-field extension at every point of a finite map is finite. -/
theorem finite_residueField_of_isFinite {X Y : Scheme.{u}} (g : X ⟶ Y) [IsFinite g]
    (x : X) :
    letI := (g.residueFieldMap x).hom.toAlgebra
    Module.Finite (Y.residueField (g x)) (X.residueField x) := by
  let : LocallyOfFiniteType g := inferInstance
  let : DiscreteTopology (g.fiber (g x)) := inferInstance
  exact (isClosed_asFiber_iff_finite_residueField g x).mp isClosed_singleton

/-- Characteristic zero reaches an actual residue field through the original
structural morphism, without identifying it with the function field. -/
theorem residueField_charZero {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    (pY : Y ⟶ Spec (.of k)) (y : Y) : CharZero (Y.residueField y) := by
  let φ : k →+* Y.residueField y :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ pY.appTop ≫ Y.Γevaluation y).hom
  exact charZero_of_injective_ringHom φ.injective

/-- In characteristic zero every actual finite-type subfield is separably generated. -/
theorem separableExtension_of_charZero (F L : Type u) [Field F] [Field L]
    [CharZero F] [Algebra F L] : Algebra.IsSeparableExtension F L := by
  constructor
  intro L' hL'
  infer_instance

variable {k : Type u} [Field k] [CharZero k] {X Y : Scheme.{u}}
variable (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k))
variable [IsCurve k pX] [IsCurve k pY] [IsProper pX] [IsProper pY]

/-- The actual fifth condition of native generic étaleness is derived
from the original nonconstant characteristic-zero curve map. -/
theorem generic_finite_separable_of_nonconstant (g : X ⟶ Y)
    (hg : g ≫ pY = pX) (hnc : ¬ ∃ y : Y, ∀ x : X, g.base x = y) :
    IsDominant g ∧
      (letI : Algebra (Y.residueField (g (genericPoint X)))
          (X.residueField (genericPoint X)) :=
        (g.residueFieldMap (genericPoint X)).hom.toAlgebra
       Module.Finite (Y.residueField (g (genericPoint X)))
          (X.residueField (genericPoint X)) ∧
       Algebra.IsSeparableExtension (Y.residueField (g (genericPoint X)))
          (X.residueField (genericPoint X))) := by
  let : IsFinite g := isFinite_of_not_constant k pX pY g hg hnc
  let : Algebra (Y.residueField (g (genericPoint X)))
      (X.residueField (genericPoint X)) :=
    (g.residueFieldMap (genericPoint X)).hom.toAlgebra
  let : CharZero (Y.residueField (g (genericPoint X))) :=
    residueField_charZero pY (g (genericPoint X))
  exact ⟨isDominant_of_not_constant k pX pY g hnc,
    finite_residueField_of_isFinite g (genericPoint X),
    separableExtension_of_charZero _ _⟩

end M9Native.CurveGenericResidueSeparable
