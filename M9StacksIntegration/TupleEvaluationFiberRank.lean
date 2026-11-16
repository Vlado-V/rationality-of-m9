module

public import M9StacksIntegration.TupleEvaluationFiber
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSheafStalkBasis

/-!
# Rank of the actual tuple evaluation on residue fibres

The free source fibre has the basis obtained by taking germs of its actual
tautological sections and extending scalars to the residue field. In these
coordinates, the native sheaf evaluation is exactly `tupleMap`.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace M9Native.TupleEvaluationFiber

variable {X : Scheme.{u}}

/-- The original source of the native tuple evaluation. -/
abbrev tupleFreeSheaf (r : ℕ) : X.Modules :=
  _root_.SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin r))

/-- The stalk basis given by the germs of the original tautological sections. -/
def freeStalkBasis (r : ℕ) (x : X) :
    Module.Basis (Fin r) (X.presheaf.stalk x)
      (ExteriorEvaluation.stalkSections (tupleFreeSheaf (X := X) r) x) := by
  classical
  exact ((Pi.basisFun (X.presheaf.stalk x) (ULift.{u} (Fin r))).map
    (Stacks.SheafOfModules.freeStalkEquiv (Osharp := X.sheaf)
      (ι := ULift.{u} (Fin r)) x)).reindex (Equiv.ulift (α := Fin r))

/-- The stalk basis is literally the germ of the original free-section generator. -/
theorem freeStalkBasis_germ (r : ℕ) (x : X) (i : Fin r) :
    freeStalkBasis r x i =
      TopCat.Presheaf.germ (tupleFreeSheaf (X := X) r).presheaf ⊤ x (by simp)
        ((_root_.SheafOfModules.freeSection (R := X.ringCatSheaf)
          (ULift.up i : ULift.{u} (Fin r))).eval (op ⊤)) := by
  classical
  let b := Pi.basisFun (X.presheaf.stalk x) (ULift.{u} (Fin r))
  let e := Stacks.SheafOfModules.freeStalkEquiv (Osharp := X.sheaf)
    (ι := ULift.{u} (Fin r)) x
  change ((b.map e).reindex (Equiv.ulift (α := Fin r))) i = _
  refine ((b.map e).reindex_apply (Equiv.ulift (α := Fin r)) i).trans ?_
  refine (b.map_apply e (ULift.up i)).trans ?_
  exact (congrArg e (Pi.basisFun_apply (X.presheaf.stalk x) (ULift.{u} (Fin r))
    (ULift.up i))).trans
      (Stacks.SheafOfModules.freeStalkEquiv_single (Osharp := X.sheaf) (x := x)
        ⊤ (by simp) (ULift.up i))

/-- The original free-source fibre basis, obtained by actual scalar extension. -/
def freeFiberBasis (r : ℕ) (x : X) :
    Module.Basis (Fin r) (X.residueField x) (Fiber (tupleFreeSheaf (X := X) r) x) :=
  letI := residueAlgebra x
  (freeStalkBasis r x).baseChange (X.residueField x)

/-- Its basis vector is the residue class of the actual free-section germ. -/
theorem freeFiberBasis_apply (r : ℕ) (x : X) (i : Fin r) :
    letI := residueAlgebra x
    freeFiberBasis r x i =
      (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ (tupleFreeSheaf (X := X) r).presheaf ⊤ x (by simp)
          ((_root_.SheafOfModules.freeSection (R := X.ringCatSheaf)
            (ULift.up i : ULift.{u} (Fin r))).eval (op ⊤)) := by
  let := residueAlgebra x
  change (freeStalkBasis r x).baseChange (X.residueField x) i = _
  rw [Module.Basis.baseChange_apply, freeStalkBasis_germ]

/-- Actual coordinates on the original free-source fibre. -/
def freeFiberCoordinates (r : ℕ) (x : X) :
    (Fin r → X.residueField x) ≃ₗ[X.residueField x]
      Fiber (tupleFreeSheaf (X := X) r) x :=
  (freeFiberBasis r x).equivFun.symm

/-- A standard coordinate is the corresponding original fibre basis vector. -/
theorem freeFiberCoordinates_single (r : ℕ) (x : X) (i : Fin r) :
    freeFiberCoordinates r x (Pi.single i 1) = freeFiberBasis r x i := by
  classical
  simp [freeFiberCoordinates, Module.Basis.equivFun_symm_apply, Pi.single_apply]

variable (k : Type u) [Field k] (f : X ⟶ Spec (.of k))

/-- On the actual free-source fibre basis, native evaluation is section evaluation. -/
theorem evaluationFiber_basis {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) (i : Fin r) :
    inducedFiberMap (MukaiSemiIrreducible.evaluation k f E s) x
      (freeFiberBasis r x i) = sectionValue k f E x (s i) := by
  let := residueAlgebra x
  rw [freeFiberBasis_apply, inducedFiberMap_tmul_germ]
  exact congrArg (fun z : Γ(E, ⊤) => (1 : X.residueField x) ⊗ₜ[X.presheaf.stalk x]
    TopCat.Presheaf.germ E.presheaf ⊤ x (by simp) z)
    (evaluation_freeSection_top k f E s i)

/-- The coordinate map of the actual sheaf evaluation is exactly the tuple's linear map. -/
theorem evaluationFiber_comp_coordinates {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    (inducedFiberMap (MukaiSemiIrreducible.evaluation k f E s) x).comp
        (freeFiberCoordinates r x).toLinearMap = tupleMap k f E s x := by
  apply (Pi.basisFun (X.residueField x) (Fin r)).ext
  intro i
  change inducedFiberMap (MukaiSemiIrreducible.evaluation k f E s) x
    (freeFiberCoordinates r x ((Pi.basisFun (X.residueField x) (Fin r)) i)) = _
  rw [Pi.basisFun_apply, freeFiberCoordinates_single, tupleMap_single]
  exact evaluationFiber_basis k f E s x i

/-- The actual sheaf evaluation and the original tuple map have the very same fibre image. -/
theorem range_tupleMap_eq_range_evaluationFiber {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    LinearMap.range (tupleMap k f E s x) =
      LinearMap.range (inducedFiberMap (MukaiSemiIrreducible.evaluation k f E s) x) := by
  rw [← evaluationFiber_comp_coordinates k f E s x]
  exact LinearMap.range_comp_of_range_eq_top _ (freeFiberCoordinates r x).range

/-- Native fibre rank of the original sheaf evaluation equals the rank of its tuple map. -/
theorem mapRankAt_evaluation_eq_finrank_tupleMap {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (x : X) :
    MukaiSemiIrreducible.mapRankAt (MukaiSemiIrreducible.evaluation k f E s) x =
      Module.finrank (X.residueField x) (LinearMap.range (tupleMap k f E s x)) := by
  change Module.finrank (X.residueField x)
    (LinearMap.range (inducedFiberMap (MukaiSemiIrreducible.evaluation k f E s) x)) = _
  rw [range_tupleMap_eq_range_evaluationFiber]

/-- The native everywhere-rank predicate is the original coordinate-map rank at every point. -/
theorem everywhereRank_evaluation_iff {r : ℕ} (E : X.Modules)
    (s : Fin r → cohomologyOverField k f E 0) (a : ℕ) :
    MukaiSemiIrreducible.EverywhereRank (MukaiSemiIrreducible.evaluation k f E s) a ↔
      ∀ x : X, Module.finrank (X.residueField x) (LinearMap.range (tupleMap k f E s x)) = a := by
  simp only [MukaiSemiIrreducible.EverywhereRank, mapRankAt_evaluation_eq_finrank_tupleMap]

end M9Native.TupleEvaluationFiber
