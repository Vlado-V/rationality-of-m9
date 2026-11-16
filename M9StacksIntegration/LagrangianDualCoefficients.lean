module

public import M9StacksIntegration.LagrangianChartCotangent
public import M9StacksIntegration.LagrangianCotangentFormula
public import StacksFrontier.AlgebraicGeometry.Reflexive.DoubleDual
public import StacksFrontier.AlgebraicGeometry.Reflexive.DualMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.Scheme

/-!
# Actual local dual coordinates of the universal quotient

All coefficient maps use the actual sheaf dual and its evaluation on
the six actual quotient sections. The local derivation is the actual
universal relative derivation, merely read as an integer derivation.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped BigOperators

universe u

namespace M9Native.LagrangianDualCoefficients

open LagrangianGrassmannian LagrangianMatrixChart
open Stacks.AlgebraicGeometry.ReflexiveModules

variable {X S : Scheme.{u}}

/-- The actual quotient section, restricted to the given open. -/
def quotientVector {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (U : X.Opens) (i : Fin 6) : Γ(Q,U) :=
  Q.presheaf.map (homOfLE (show U≤⊤ from le_top)).op (q.app ⊤ (freeVector X i))

theorem quotientVector_map {Q : X.Modules} (q : freeOn X 6 ⟶ Q) {U V : X.Opens}
    (h : V≤U) (i : Fin 6) :
    Q.presheaf.map (homOfLE h).op (quotientVector q U i)=quotientVector q V i := by
  unfold quotientVector
  rw [← ConcreteCategory.comp_apply,← Q.presheaf.map_comp]
  rfl

/-- The six actual local coefficient functions of a local functional
on the original quotient bundle. -/
def coefficientMap {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (U : X.Opens) :
    Γ(dualSheaf Q,U) →ₗ[Γ(X,U)] (Fin 6 → Γ(X,U)) :=
  LinearMap.pi (fun i =>
    { toFun := fun α => evalAt Q α (quotientVector q U i)
      map_add' α β := evalAt_add Q α β _
      map_smul' r α := by simpa only [RingHom.id_apply] using evalAt_smul Q r α _ })

@[simp] theorem coefficientMap_apply {Q : X.Modules} (q : freeOn X 6 ⟶ Q) (U : X.Opens)
    (α : Γ(dualSheaf Q,U)) (i : Fin 6) :
    coefficientMap q U α i=evalAt Q α (quotientVector q U i) := rfl

/-- The actual dual coefficient map commutes with every restriction. -/
theorem coefficientMap_map {Q : X.Modules} (q : freeOn X 6 ⟶ Q) {U V : X.Opens}
    (h : V≤U) (α : Γ(dualSheaf Q,U)) (i : Fin 6) :
    coefficientMap q V ((dualSheaf Q).presheaf.map (homOfLE h).op α) i=
      X.presheaf.map (homOfLE h).op (coefficientMap q U α i) := by
  change evalAt Q ((dualSheaf Q).presheaf.map (homOfLE h).op α) (quotientVector q V i)= _
  rw [← quotientVector_map q h i]
  exact evalAt_map Q h α _

/-- A local section of the actual dual is an actual morphism on the
open subscheme. No trivialization or pointwise replacement is used. -/
def localFunctional (Q : X.Modules) (U : X.Opens) (α : Γ(dualSheaf Q,U)) :
    (Scheme.Modules.restrictFunctor U.ι).obj Q ⟶ SheafOfModules.unit (U : Scheme.{u}).ringCatSheaf :=
  ((Scheme.Modules.overFunctorEquiv U).app Q).inv ≫
    (Scheme.Modules.overEquiv U).functor.map
      (⟨α⟩ : Q.over U ⟶ (SheafOfModules.unit X.ringCatSheaf).over U) ≫
    ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).hom ≫
    (Scheme.Modules.restrictUnitIso U.ι).hom

/-- The genuine relative universal derivation on a fixed open, read
as an ordinary integer derivation. This changes no underlying function. -/
def localDerivation (p : X ⟶ S) (U : X.Opens) :
    Derivation ℤ Γ(X,U) Γ(Scheme.Hom.relativeDifferentials p,U) where
  toLinearMap := ((Scheme.Hom.universalRelativeDerivation p).d (X := op U)).toIntLinearMap
  map_one_eq_zero' := (Scheme.Hom.universalRelativeDerivation p).d_one (op U)
  leibniz' := (Scheme.Hom.universalRelativeDerivation p).d_mul

@[simp] theorem localDerivation_apply (p : X ⟶ S) (U : X.Opens) (r : Γ(X,U)) :
    localDerivation p U r=(Scheme.Hom.universalRelativeDerivation p).d r := rfl

theorem localDerivation_map (p : X ⟶ S) {U V : X.Opens} (h : V≤U) (r : Γ(X,U)) :
    localDerivation p V (X.presheaf.map (homOfLE h).op r)=
      (Scheme.Hom.relativeDifferentials p).presheaf.map (homOfLE h).op
        (localDerivation p U r) :=
  (Scheme.Hom.universalRelativeDerivation p).d_map (homOfLE h).op r

/-- The literal native symmetric square sheaf used by the global
cotangent comparison. -/
abbrev symmetricSquare (Q : X.Modules) : X.Modules :=
  (Scheme.Modules.symmetricAlgebra X Q).piece 2

end M9Native.LagrangianDualCoefficients
